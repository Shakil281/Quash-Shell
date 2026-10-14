/*
 * Quash - Project 1: Create Your Own Shell
 * Author: Shakil Ahmed Faisal
 *
 * Features:
 *   - Prompt shows the current working directory (e.g. /home/codio> )
 *   - Built-ins: cd, pwd, echo, exit, env, setenv
 *   - $VAR expansion in any command's arguments
 *   - External programs via fork() + execvp()
 *   - Background processes with a trailing &
 *   - Ctrl-C kills the foreground process, not the shell
 *   - Foreground processes are killed after 10 seconds
 *   - I/O redirection (<, >, >>) and pipes (|), including multi-stage pipes
 */
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#define MAX_COMMAND_LINE_LEN 1024
#define MAX_COMMAND_LINE_ARGS 128
#define MAX_PIPELINE 16
#define TIMEOUT_SECONDS 10

char prompt[] = "> ";
char delimiters[] = " \t\r\n";
extern char **environ;

/* Foreground children the shell is currently waiting on.
 * The signal handlers read these to know whom to kill. */
static volatile pid_t fg_pids[MAX_PIPELINE];
static volatile sig_atomic_t fg_count = 0;

/* The prompt is built ahead of time so the SIGINT handler can reprint it
 * using only async-signal-safe calls. */
static char prompt_buf[MAX_COMMAND_LINE_LEN + 8];
static volatile size_t prompt_len = 0;

/* ------------------------------------------------------------------ */
/* Signal handling                                                     */
/* ------------------------------------------------------------------ */

static void safe_write(const char *s, size_t len) {
    ssize_t r = write(STDOUT_FILENO, s, len);
    (void)r;
}

static void kill_foreground(int sig) {
    for (int i = 0; i < fg_count; i++) {
        if (fg_pids[i] > 0) {
            kill(fg_pids[i], sig);
        }
    }
}

/* Ctrl-C: stop the foreground job (if any) and keep the shell alive. */
static void sigint_handler(int sig) {
    (void)sig;
    safe_write("\n", 1);
    if (fg_count > 0) {
        kill_foreground(SIGINT);
    } else {
        safe_write(prompt_buf, prompt_len);  /* Ctrl-C at an empty prompt */
    }
}

/* Timer expired: the foreground job ran longer than TIMEOUT_SECONDS. */
static void sigalrm_handler(int sig) {
    (void)sig;
    kill_foreground(SIGKILL);
}

static void install_signal_handlers(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;  /* restart fgets()/waitpid() after a signal */

    sa.sa_handler = sigint_handler;
    sigaction(SIGINT, &sa, NULL);

    sa.sa_handler = sigalrm_handler;
    sigaction(SIGALRM, &sa, NULL);
}

/* ------------------------------------------------------------------ */
/* Prompt and parsing                                                  */
/* ------------------------------------------------------------------ */

static void update_prompt(void) {
    char cwd[MAX_COMMAND_LINE_LEN];
    if (getcwd(cwd, sizeof(cwd)) == NULL) {
        perror("getcwd() failed");
        cwd[0] = '\0';
    }
    snprintf(prompt_buf, sizeof(prompt_buf), "%s%s", cwd, prompt);
    prompt_len = strlen(prompt_buf);
}

/*
 * Splits the line into tokens in place. Text inside "double" or 'single'
 * quotes becomes one token without the quotes, so  grep "this"  works.
 * An unquoted token starting with $ is replaced by that environment
 * variable's value (unset variables are dropped, like bash).
 * Returns the number of tokens; args is NULL-terminated.
 */
static int tokenize(char *line, char **args) {
    int n = 0;
    char *p = line;

    while (*p != '\0' && n < MAX_COMMAND_LINE_ARGS - 1) {
        while (*p != '\0' && strchr(delimiters, *p) != NULL) {
            p++;
        }
        if (*p == '\0') {
            break;
        }

        char *tok;
        bool quoted = false;
        if (*p == '"' || *p == '\'') {
            char quote = *p++;
            tok = p;
            while (*p != '\0' && *p != quote) {
                p++;
            }
            quoted = true;
        } else {
            tok = p;
            while (*p != '\0' && strchr(delimiters, *p) == NULL) {
                p++;
            }
        }
        if (*p != '\0') {
            *p++ = '\0';
        }

        if (!quoted && tok[0] == '$' && tok[1] != '\0') {
            char *value = getenv(tok + 1);
            if (value == NULL) {
                continue;
            }
            tok = value;
        }
        args[n++] = tok;
    }

    args[n] = NULL;
    return n;
}

/* Removes a trailing & (either "cmd &" or "cmd&"). Returns true if found. */
static bool strip_background(char **args, int *argc) {
    if (*argc == 0) {
        return false;
    }
    char *last = args[*argc - 1];
    if (strcmp(last, "&") == 0) {
        args[--(*argc)] = NULL;
        return true;
    }
    size_t len = strlen(last);
    if (len > 1 && last[len - 1] == '&') {
        last[len - 1] = '\0';
        return true;
    }
    return false;
}

/*
 * Handles <, > and >> in args: opens the files, points stdin/stdout at them
 * with dup2(), and removes the operators and file names from args.
 * Returns 0 on success, -1 on error.
 */
static int apply_redirections(char **args) {
    int i = 0, j = 0;
    while (args[i] != NULL) {
        bool in = strcmp(args[i], "<") == 0;
        bool out = strcmp(args[i], ">") == 0;
        bool append = strcmp(args[i], ">>") == 0;

        if (!in && !out && !append) {
            args[j++] = args[i++];
            continue;
        }
        if (args[i + 1] == NULL) {
            fprintf(stderr, "syntax error: expected a file name after %s\n", args[i]);
            return -1;
        }

        int fd, target;
        if (in) {
            fd = open(args[i + 1], O_RDONLY);
            target = STDIN_FILENO;
        } else {
            int flags = O_WRONLY | O_CREAT | (append ? O_APPEND : O_TRUNC);
            fd = open(args[i + 1], flags, 0644);
            target = STDOUT_FILENO;
        }
        if (fd < 0) {
            perror(args[i + 1]);
            return -1;
        }
        if (dup2(fd, target) < 0) {
            perror("dup2() failed");
            close(fd);
            return -1;
        }
        close(fd);
        i += 2;
    }
    args[j] = NULL;
    return 0;
}

/* ------------------------------------------------------------------ */
/* Built-in commands                                                   */
/* ------------------------------------------------------------------ */

static bool is_builtin(const char *cmd) {
    static const char *names[] = {"cd", "pwd", "echo", "exit", "env", "setenv", NULL};
    for (int i = 0; names[i] != NULL; i++) {
        if (strcmp(cmd, names[i]) == 0) {
            return true;
        }
    }
    return false;
}

static void run_builtin(char **args) {
    const char *cmd = args[0];

    if (strcmp(cmd, "cd") == 0) {
        const char *target = args[1] != NULL ? args[1] : getenv("HOME");
        if (target == NULL) {
            fprintf(stderr, "cd: HOME not set\n");
        } else if (chdir(target) != 0) {
            perror("cd");
        }

    } else if (strcmp(cmd, "pwd") == 0) {
        char cwd[MAX_COMMAND_LINE_LEN];
        if (getcwd(cwd, sizeof(cwd)) != NULL) {
            printf("%s\n", cwd);
        } else {
            perror("pwd");
        }

    } else if (strcmp(cmd, "echo") == 0) {
        for (int i = 1; args[i] != NULL; i++) {
            printf("%s%s", i > 1 ? " " : "", args[i]);
        }
        printf("\n");

    } else if (strcmp(cmd, "exit") == 0) {
        exit(0);

    } else if (strcmp(cmd, "env") == 0) {
        if (args[1] != NULL) {
            /* env NAME [NAME...] prints just those values */
            for (int i = 1; args[i] != NULL; i++) {
                char *value = getenv(args[i]);
                if (value != NULL) {
                    printf("%s\n", value);
                }
            }
        } else {
            for (char **e = environ; *e != NULL; e++) {
                printf("%s\n", *e);
            }
        }

    } else if (strcmp(cmd, "setenv") == 0) {
        /* Accepts both "setenv NAME=VALUE" and "setenv NAME VALUE". */
        char *name = args[1];
        const char *value = args[1] != NULL ? args[2] : NULL;
        if (name == NULL) {
            fprintf(stderr, "usage: setenv NAME=VALUE\n");
            return;
        }
        char *eq = strchr(name, '=');
        if (eq != NULL) {
            *eq = '\0';
            value = eq + 1;
        }
        if (value == NULL) {
            value = "";
        }
        if (setenv(name, value, 1) != 0) {
            perror("setenv");
        }
    }
}

/* Runs a built-in in the shell process, with optional < / > redirection. */
static void run_builtin_redirected(char **args) {
    fflush(stdout);
    int saved_in = dup(STDIN_FILENO);
    int saved_out = dup(STDOUT_FILENO);

    if (apply_redirections(args) == 0 && args[0] != NULL) {
        run_builtin(args);
    }

    fflush(stdout);
    dup2(saved_in, STDIN_FILENO);
    dup2(saved_out, STDOUT_FILENO);
    close(saved_in);
    close(saved_out);
}

/* ------------------------------------------------------------------ */
/* External commands, background jobs, pipes                           */
/* ------------------------------------------------------------------ */

/* Runs in the child after fork(): set up redirection, then execvp(). */
static void exec_child(char **args) {
    signal(SIGINT, SIG_DFL);
    signal(SIGALRM, SIG_DFL);

    if (apply_redirections(args) < 0) {
        exit(1);
    }
    if (args[0] == NULL) {
        exit(0);
    }
    execvp(args[0], args);

    /* Only reached if execvp() failed. */
    perror("execvp() failed");
    printf("An error occurred.\n");
    fflush(stdout);
    exit(1);
}

/*
 * Runs "cmd1 | cmd2 | ... | cmdN" (N may be 1). Each stage is a child
 * process; stage k's stdout is connected to stage k+1's stdin with pipe().
 * Foreground jobs are waited on with a 10-second timer; background jobs
 * are left running and reaped later in the main loop.
 */
static void run_pipeline(char **args, int argc, bool background) {
    char **cmds[MAX_PIPELINE];
    int ncmds = 0;
    cmds[ncmds++] = args;

    for (int i = 0; i < argc; i++) {
        if (args[i] != NULL && strcmp(args[i], "|") == 0) {
            if (ncmds == MAX_PIPELINE) {
                fprintf(stderr, "too many pipes\n");
                return;
            }
            args[i] = NULL;
            cmds[ncmds++] = &args[i + 1];
        }
    }
    for (int k = 0; k < ncmds; k++) {
        if (cmds[k][0] == NULL) {
            fprintf(stderr, "syntax error near |\n");
            return;
        }
    }

    pid_t pids[MAX_PIPELINE];
    int launched = 0;
    int prev_read = -1;

    fflush(stdout);  /* don't let the child inherit unflushed output */

    for (int k = 0; k < ncmds; k++) {
        int fd[2] = {-1, -1};
        if (k < ncmds - 1 && pipe(fd) < 0) {
            perror("pipe() failed");
            break;
        }

        pid_t pid = fork();
        if (pid < 0) {
            perror("fork() failed");
            if (fd[0] != -1) {
                close(fd[0]);
                close(fd[1]);
            }
            break;
        }

        if (pid == 0) {
            if (background) {
                setpgid(0, 0);  /* so Ctrl-C at the terminal doesn't hit it */
            }
            if (prev_read != -1) {
                dup2(prev_read, STDIN_FILENO);
                close(prev_read);
            }
            if (fd[1] != -1) {
                dup2(fd[1], STDOUT_FILENO);
                close(fd[0]);
                close(fd[1]);
            }
            exec_child(cmds[k]);
        }

        pids[launched++] = pid;
        if (prev_read != -1) {
            close(prev_read);
        }
        if (fd[1] != -1) {
            close(fd[1]);
        }
        prev_read = fd[0];
    }
    if (prev_read != -1) {
        close(prev_read);
    }

    if (background || launched == 0) {
        return;
    }

    /* Foreground: wait, but kill the job if it runs past the time limit. */
    for (int k = 0; k < launched; k++) {
        fg_pids[k] = pids[k];
    }
    fg_count = launched;
    alarm(TIMEOUT_SECONDS);

    for (int k = 0; k < launched; k++) {
        int status;
        while (waitpid(pids[k], &status, 0) < 0 && errno == EINTR) {
        }
    }

    alarm(0);
    fg_count = 0;
}

/* ------------------------------------------------------------------ */
/* Main loop                                                           */
/* ------------------------------------------------------------------ */

int main() {
    // Stores the string typed into the command line.
    char command_line[MAX_COMMAND_LINE_LEN];
    char cmd_bak[MAX_COMMAND_LINE_LEN];

    // Stores the tokenized command line input.
    char *arguments[MAX_COMMAND_LINE_ARGS];

    install_signal_handlers();

    while (true) {

        do {
            // Clean up any background jobs that have finished.
            while (waitpid(-1, NULL, WNOHANG) > 0) {
            }

            // Print the shell prompt: <current directory>>
            update_prompt();
            printf("%s", prompt_buf);
            fflush(stdout);

            // Read input from stdin and store it in command_line.
            if (fgets(command_line, MAX_COMMAND_LINE_LEN, stdin) == NULL) {
                if (ferror(stdin)) {
                    fprintf(stderr, "fgets error");
                }
                exit(0);  // error or end of input (Ctrl-D)
            }

        } while (command_line[0] == 0x0A);  // while just ENTER pressed

        strcpy(cmd_bak, command_line);

        int argc = tokenize(command_line, arguments);
        bool background = strip_background(arguments, &argc);
        if (argc == 0) {
            continue;
        }
        assert(arguments[argc] == NULL);

        bool has_pipe = false;
        for (int i = 0; i < argc; i++) {
            if (strcmp(arguments[i], "|") == 0) {
                has_pipe = true;
            }
        }

        if (!has_pipe && is_builtin(arguments[0])) {
            run_builtin_redirected(arguments);
        } else {
            run_pipeline(arguments, argc, background);
        }
    }

    // This should never be reached.
    return -1;
}
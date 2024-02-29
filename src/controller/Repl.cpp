//
// Created by fedora on 5/25/22.
//

#include "Repl.h"
#include "common.h"

#include <unistd.h>
#include <readline/readline.h>
#include <readline/history.h>

void Repl::readline() {
    char *line;
#define CHECK_ARGS(argc) if (!c.check_prompt_invalid(argc)) continue; else cerr_verbose << "Read cmd: " << c << endl
    while ((line = ::readline(prompt)) != NULL) {
        cmd_t c(line);
        if (c.empty())
            continue;
        add_history(line);
        if (c.get_cmd() == "file") {
            CHECK_ARGS(2);
            command.read_file(c.get_arg(1));
            continue;
        } else if (c.get_cmd() == "exit") {
            break;
        }
        command.enqueue(std::move(c));
        free(line);
        if (prompt)
            usleep(100000);
    }
    command.enqueue("exit");
}

Repl::Repl() {
    if (!isatty(STDIN_FILENO))
        prompt = NULL;
}

//
// Created by fedora on 8/26/23.
//

#ifndef STATE_COLLECTOR_H
#define STATE_COLLECTOR_H

#include <unistd.h>

void write_log(int fd, const char *buf, size_t count);
int collect_states();
char* get_state(const char* var);  // must be freed after use
void state_collect_thread();

#endif //STATE_COLLECTOR_H

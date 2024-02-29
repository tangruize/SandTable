//
// Created by fedora on 8/26/23.
//

#include <string>
#include <map>
#include <sstream>

using namespace std;

static string last_log_buf;
static map<string, string> states;
#ifdef GET_STATE_USE_STATIC_BUF
#define VAR_BUF_SIZE 2048
static char var_buf[VAR_BUF_SIZE];
#endif

extern "C" {

#include "config.h"
#include "common.h"
#include "state_collector.h"
#include "mysyscall.h"
#include <sys/wait.h>

static pthread_mutex_t state_mutex = PTHREAD_MUTEX_INITIALIZER;

static void clear_states() {
    states.clear();
}

// must be freed after use
char* get_state(const char* var) {
    char *ret;
    pthread_mutex_lock(&state_mutex);
    auto it = states.find(var);
    if (it == states.end()) {
        pthread_mutex_unlock(&state_mutex);
        print_info_no_prompt("  - WARN: variable \"%s\" not found\n", var);
        return NULL;
    }
    ret = (char*)malloc(it->second.size() + 1);
    memcpy(ret, it->second.c_str(), it->second.size() + 1);
    pthread_mutex_unlock(&state_mutex);
    print_info_no_prompt("  - %s=%s\n", var, ret);
    return ret;
}

void write_log(int fd, const char *buf, size_t count) {
    if (_syscall_(SYS_write, fd, buf, count) == -1) {
        print_info("WARN: failed to write log fd %d, size %d\n", fd, count);
        return;
    }
    pthread_mutex_lock(&state_mutex);
    last_log_buf.append(buf, count);
    pthread_mutex_unlock(&state_mutex);
}

int collect_states() {
    pthread_mutex_lock(&state_mutex);
    if (!option_state_no_clear)
        clear_states();
    string last_log_buf_tmp = last_log_buf + '\n';
    last_log_buf.clear();
    pthread_mutex_unlock(&state_mutex);
    ssize_t ret;
    ret = _syscall_(SYS_write, collector_childinfo.to_child, last_log_buf_tmp.c_str(), last_log_buf_tmp.size());
    if (ret == -1) {
        print_info("WARN: failed to write state collector pipe: %s\n", strerror(errno));
        return false;
    }
    return true;
}

void state_collect_thread() {
    FILE *fp = fdopen(collector_childinfo.from_child, "r");
    if (!fp) {
        print_info_no_prompt("  - WARN: fdopen failed: %s\n", strerror(errno));
        return;
    }
    print_info("State collector started\n");
    char *key = NULL, *value = NULL;
    size_t key_len = 0, value_len = 0;
    ssize_t nread;
    while (true) {
        nread = getdelim(&key, &key_len, '=', fp);
        if (nread == -1 || nread == 0)
            break;
        if (nread > 0 && key[nread - 1] == '=')
            key[nread - 1] = 0;
        nread = getdelim(&value, &value_len, '\n', fp);
        if (nread == -1 || nread == 0)
            break;
        if (nread > 0 && value[nread - 1] == '\n')
            value[nread - 1] = 0;
        char *p = key;
        while (*p == '\n') p++;
        print_info_no_prompt("  - %s=%s\n", p, value);
        pthread_mutex_lock(&state_mutex);
        states[p] = value;
        pthread_mutex_unlock(&state_mutex);
    }
    print_info("State collector is exiting...\n");
    free(key);
    free(value);
    fclose(fp);
    waitpid(collector_childinfo.child_pid, NULL, 0);
    print_info("State collector exited\n");
}

} // extern "C"
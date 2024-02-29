//
// Created by fedora on 5/26/22.
//

#include "common.h"
#include "myrandom.h"

MAKE_LIB_TEMPLATE(long, random, void) {
    if (check_count_intercepted(LIB_random)) {
        LOG_INTERCEPTED(LIB_random, "hack random return 1");
        return 1;
    }
    return real_random();
}

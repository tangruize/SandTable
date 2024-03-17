//
// Created by tangruize on 2/14/23.
//

#ifndef REDISTMET_RAFT_H
#define REDISTMET_RAFT_H

#include "common.h"

bool RaftRepl(const string &cmd);
string RaftGet(const string &variable);

#endif //REDISTMET_RAFT_H

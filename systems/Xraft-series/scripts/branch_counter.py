counter = {
    "Init": 0,
    "ElectionTimeout": 0,
    "RecvRequestVote": {
        "not-vote: term bigger": 0,
        "not-vote: step down log newer": 0,
        "not-vote: voted for self": 0,
        "not-vote: voted or log newer": 0,
        "voted": 0,
    },
    "RecvRequestVoteResponse": {
        "term is smaller": 0,
        "not candidate or term mismatch": 0,
        "become leader": 0,
        "granted": 0,
        "not granted": 0,
    },
    "SendAppendentriesAll": 0,
    "RecvAppendentries": {
        "term is bigger": 0,
        "no prev log": 0,
        "term mismatch": 0,
        "success": 0,
    },
    "RecvAppendentriesResponse": {
        "stale msg": 0,
        "term is smaller": 0,
        "not leader": 0,
        "fail retry": 0,
        "success": 0,
        "success retry": 0,
    },
    "RecvEntry": 0,
    "ClientGetValue": 0,
    "DoNetworkPartition": 0,
    "DoNetworkCure": 0,
}

jq_cmd_str = '.[] | .netcmd | .[0] | .[0:2]'
jq_inv_str = '.[] | .inv | .[]'

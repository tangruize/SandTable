include $(dir $(realpath $(lastword $(MAKEFILE_LIST))))/../../Makefile.inc

_check_pysyncobj_bug:
	@test ${BUG_DIR}
	${BACKEND} exec ${INTERACTIVE_OR_SEP} ${CONTROLLER_NODE} rm -rf '/root/sandtable/systems/PySyncObj/bugs/${BUG_DIR}/mc'
	${BACKEND} exec ${INTERACTIVE_OR_SEP} ${CONTROLLER_NODE} sh -c "cd /root/sandtable/systems/PySyncObj/bugs/${BUG_DIR} && python3 /root/sandtable/scripts/tlcwrapper.py -s MC.ini"
	${BACKEND} exec ${INTERACTIVE_OR_SEP} ${CONTROLLER_NODE} sh -c "cd /root/sandtable/systems/PySyncObj/bugs/${BUG_DIR}/mc && find -name MC.out | xargs ls -t | head -1 | xargs python3 /root/sandtable/scripts/trace_reader.py | jq -c '.[].netcmd[0]'"

_replay_pysyncobj_bug:
	@test ${BUG_DIR}
	@test ${N_SERVERS}
	${BACKEND} exec ${INTERACTIVE_OR_SEP} ${CONTROLLER_NODE} rm -rf /root/sandtable/systems/PySyncObj/bugs/${BUG_DIR}/test
	${BACKEND} exec ${INTERACTIVE_OR_SEP} ${CONTROLLER_NODE} env BACKEND=${BACKEND} /root/sandtable/systems/PySyncObj/scripts/run_one_testcase.sh /root/sandtable/systems/PySyncObj/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/PySyncObj/bugs/${BUG_DIR}/test

check_pysyncobj_leader_commits_older_terms_bug:
	make _check_pysyncobj_bug BUG_DIR=leader_commits_older_terms

replay_pysyncobj_leader_commits_older_terms_bug:
	make _replay_pysyncobj_bug BUG_DIR=leader_commits_older_terms N_SERVERS=3

check_pysyncobj_non_monotonic_commit_idx_bug:
	make _check_pysyncobj_bug BUG_DIR=non_monotonic_commit_idx

replay_pysyncobj_non_monotonic_commit_idx_bug:
	make _replay_pysyncobj_bug BUG_DIR=non_monotonic_commit_idx N_SERVERS=2

check_pysyncobj_next_idx_no_greater_than_match_idx_bug:
	make _check_pysyncobj_bug BUG_DIR=next_idx_no_greater_than_match_idx

replay_pysyncobj_next_idx_no_greater_than_match_idx_bug:
	make _replay_pysyncobj_bug BUG_DIR=next_idx_no_greater_than_match_idx N_SERVERS=2

check_pysyncobj_non_monotonic_match_idx_bug:
	make _check_pysyncobj_bug BUG_DIR=non_monotonic_match_idx

replay_pysyncobj_non_monotonic_match_idx_bug:
	make _replay_pysyncobj_bug BUG_DIR=non_monotonic_match_idx N_SERVERS=2

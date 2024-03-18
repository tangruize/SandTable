_replay_pysyncobj_bug:
	docker exec -it controller rm -rf /root/sandtable/systems/PySyncObj/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/PySyncObj/scripts/run_one_testcase.sh /root/sandtable/systems/PySyncObj/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/PySyncObj/bugs/${BUG_DIR}/test

replay_pysyncobj_leader_commits_older_terms_bug:
	make _replay_pysyncobj_bug BUG_DIR=leader_commits_older_terms N_SERVERS=3

replay_pysyncobj_non_monotonic_commit_idx_bug:
	make _replay_pysyncobj_bug BUG_DIR=non_monotonic_commit_idx N_SERVERS=2

replay_pysyncobj_next_idx_no_greater_than_match_idx_bug:
	make _replay_pysyncobj_bug BUG_DIR=next_idx_no_greater_than_match_idx N_SERVERS=2

replay_pysyncobj_non_monotonic_match_idx_bug:
	make _replay_pysyncobj_bug BUG_DIR=non_monotonic_match_idx N_SERVERS=2

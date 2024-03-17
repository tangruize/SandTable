_replay_wraft_series_bug:
	docker exec -it controller rm -rf /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/scripts/run_one_testcase.sh /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/test

replay_wraft_inconsistent_committed_log_bug:
	make _replay_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=inconsistent_committed_log N_SERVERS=3

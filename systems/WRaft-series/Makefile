_check_wraft_series_bug:
	@test ${BUG_SYSTEM}
	@test ${BUG_DIR}
	docker exec controller rm -rf '/root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/mc'
	docker exec -it controller sh -c "cd /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR} && python3 /root/sandtable/scripts/tlcwrapper.py -s MC.ini"
	docker exec controller sh -c "find /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/mc -name MC.out | xargs ls -t | head -1 | xargs python3 /root/sandtable/scripts/trace_reader.py | jq -c '.[] | .scr.pc,.netcmd[0] | select( . != null )'"

_replay_wraft_series_bug:
	@test ${BUG_SYSTEM}
	@test ${BUG_DIR}
	@test ${N_SERVERS}
	docker exec controller rm -rf /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/scripts/run_one_testcase.sh /root/sandtable/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/WRaft-series/${BUG_SYSTEM}/bugs/${BUG_DIR}/test

check_wraft_inconsistent_committed_log_bug:
	make _check_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=inconsistent_committed_log

replay_wraft_inconsistent_committed_log_bug:
	make _replay_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=inconsistent_committed_log N_SERVERS=3

check_wraft_incorrect_appending_entries_bug:
	make _check_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=incorrect_appending_entries

replay_wraft_incorrect_appending_entries_bug:
	make _replay_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=incorrect_appending_entries N_SERVERS=3

check_wraft_next_idx_no_greater_than_match_idx_bug:
	make _check_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=next_idx_no_greater_than_match_idx

replay_wraft_next_idx_no_greater_than_match_idx_bug:
	make _replay_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=next_idx_no_greater_than_match_idx N_SERVERS=3

check_wraft_non_monotonic_current_term_bug:
	make _check_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=non_monotonic_current_term

replay_wraft_non_monotonic_current_term_bug:
	make _replay_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=non_monotonic_current_term N_SERVERS=3

check_wraft_retry_empty_logs_bug:
	make _check_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=retry_empty_logs

replay_wraft_retry_empty_logs_bug:
	make _replay_wraft_series_bug BUG_SYSTEM=WRaft BUG_DIR=retry_empty_logs N_SERVERS=3

check_daosraft_leader_votes_for_others_bug:
	make _check_wraft_series_bug BUG_SYSTEM=DaosRaft BUG_DIR=leader_votes_for_others

replay_daosraft_leader_votes_for_others_bug:
	make _replay_wraft_series_bug BUG_SYSTEM=DaosRaft BUG_DIR=leader_votes_for_others N_SERVERS=2

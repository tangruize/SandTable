raftos_deploy_venv:
	docker exec controller sh -c 'if ! test -d /root/sandtable/systems/RaftOS/raftos/venv; then cd /root/sandtable/systems/RaftOS/raftos && tar xzf venv.tar.gz; fi'

_check_raftos_bug:
	@test ${BUG_DIR}
	docker exec controller rm -rf '/root/sandtable/systems/RaftOS/bugs/${BUG_DIR}/mc'
	docker exec -it controller sh -c "cd /root/sandtable/systems/RaftOS/bugs/${BUG_DIR} && python3 /root/sandtable/scripts/tlcwrapper.py -s MC.ini"
	docker exec controller sh -c "cd /root/sandtable/systems/RaftOS/bugs/${BUG_DIR}/mc && find -name MC.out | xargs ls -t | head -1 | xargs python3 /root/sandtable/scripts/trace_reader.py | jq -c '.[].netcmd[0]'"

_replay_raftos_bug: raftos_deploy_venv
	@test ${BUG_DIR}
	@test ${N_SERVERS}
	docker exec controller rm -rf /root/sandtable/systems/RaftOS/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/RaftOS/scripts/run_one_testcase.sh /root/sandtable/systems/RaftOS/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/RaftOS/bugs/${BUG_DIR}/test

check_raftos_commitment_not_advanced_bug:
	make _check_raftos_bug BUG_DIR=commitment_not_advanced

replay_raftos_commitment_not_advanced_bug:
	make _replay_raftos_bug BUG_DIR=commitment_not_advanced N_SERVERS=2

check_incorrect_erasing_entries_bug:
	make _check_raftos_bug BUG_DIR=incorrect_erasing_entries

replay_raftos_incorrect_erasing_entries_bug:
	make _replay_raftos_bug BUG_DIR=incorrect_erasing_entries N_SERVERS=2

check_non_monotonic_match_idx_bug:
	make _check_raftos_bug BUG_DIR=non_monotonic_match_idx

replay_raftos_non_monotonic_match_idx_bug:
	make _replay_raftos_bug BUG_DIR=non_monotonic_match_idx N_SERVERS=2

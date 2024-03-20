raftos_deploy_venv:
	docker exec controller sh -c 'cd /root/sandtable/systems/RaftOS/raftos && tar xzf venv.tar.gz'

_replay_raftos_bug:
	docker exec -it controller rm -rf /root/sandtable/systems/RaftOS/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/RaftOS/scripts/run_one_testcase.sh /root/sandtable/systems/RaftOS/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/RaftOS/bugs/${BUG_DIR}/test

replay_raftos_commitment_not_advanced_bug:
	make _replay_raftos_bug BUG_DIR=commitment_not_advanced N_SERVERS=2

replay_raftos_incorrect_erasing_entries_bug:
	make _replay_raftos_bug BUG_DIR=incorrect_erasing_entries N_SERVERS=2

replay_raftos_non_monotonic_match_idx_bug:
	make _replay_raftos_bug BUG_DIR=non_monotonic_match_idx N_SERVERS=2

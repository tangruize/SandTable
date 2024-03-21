_check_xraft_series_bug:
	docker exec controller rm -rf '/root/sandtable/systems/Xraft-series/bugs/${BUG_DIR}/mc'
	docker exec -it controller sh -c "cd /root/sandtable/systems/Xraft-series/bugs/${BUG_DIR} && python3 /root/sandtable/scripts/tlcwrapper.py -s MC.ini"
	docker exec controller sh -c "cd /root/sandtable/systems/Xraft-series/bugs/${BUG_DIR}/mc && find -name MC.out | xargs ls -t | head -1 | xargs python3 /root/sandtable/scripts/trace_reader.py | jq -c '.[].netcmd[0]'"

_replay_xraft_series_bug:
	docker exec controller rm -rf /root/sandtable/systems/Xraft-series/bugs/${BUG_DIR}/test
	docker exec -it controller /root/sandtable/systems/Xraft-series/scripts/run_one_testcase.sh /root/sandtable/systems/Xraft-series/bugs/${BUG_DIR}/MC.out ${N_SERVERS}
	echo ==== Replay logs location: build/mount/systems/Xraft-series/bugs/${BUG_DIR}/test

check_xraft_election_safety_bug:
	make _check_xraft_series_bug BUG_DIR=election_safety

replay_xraft_election_safety_bug:
	make _replay_xraft_series_bug BUG_DIR=election_safety N_SERVERS=3
	grep -r "become leader, term" build/mount/systems/Xraft-series/bugs/election_safety/test/log*

check_xraft_kv_linearizability_bug:
	make _check_xraft_series_bug BUG_DIR=linearizability

replay_xraft_kv_linearizability_bug:
	make _replay_xraft_series_bug BUG_DIR=linearizability N_SERVERS=3

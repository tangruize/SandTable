check_zookeeper_vote_circle_bug:
	docker exec controller rm -rf '/root/sandtable/systems/ZooKeeper/v3.4.3/bugs/vote_circle/mc'
	docker exec -it controller sh -c "cd /root/sandtable/systems/ZooKeeper/v3.4.3/bugs/vote_circle && python3 /root/sandtable/scripts/tlcwrapper.py -s MC.ini"
	docker exec controller sh -c "cd /root/sandtable/systems/ZooKeeper/v3.4.3/bugs/vote_circle/mc && find -name MC.out | xargs ls -t | head -1 | xargs python3 /root/sandtable/scripts/trace_reader.py | jq -c '.[].netcmd[0]'"

replay_zookeeper_vote_circle_bug:
	docker exec controller rm -rf /root/sandtable/systems/ZooKeeper/v3.4.3/bugs/vote_circle/test
	docker exec -it controller /root/sandtable/systems/ZooKeeper/v3.4.3/scripts/run_one_testcase.sh /root/sandtable/systems/ZooKeeper/v3.4.3/bugs/vote_circle/MC.out
	echo ==== Replay logs location: build/mount/systems/ZooKeeper/v3.4.3/bugs/vote_circle/test
	grep -E '(- Updating proposal)' build/mount/systems/ZooKeeper/v3.4.3/bugs/vote_circle/test/node_log.1

replay_zookeeper_vote_circle_bug:
	docker exec -it controller rm -rf /root/sandtable/systems/ZooKeeper/v3.4.3/bugs/vote_circle/test
	docker exec -it controller /root/sandtable/systems/ZooKeeper/v3.4.3/scripts/run_one_testcase.sh /root/sandtable/systems/ZooKeeper/v3.4.3/bugs/vote_circle/MC.out
	echo ==== Replay logs location: build/mount/systems/ZooKeeper/v3.4.3/bugs/vote_circle/test
	grep -E '(- Updating proposal)' build/mount/systems/ZooKeeper/v3.4.3/bugs/vote_circle/test/node_log.1

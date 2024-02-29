BUILD_DIR := .

ifeq ($(wildcard /.dockerenv),)
    # not in docker
    BUILD_DIR := build
endif

build-sandtable:
	@test -f /.dockerenv || echo "Warning: SandTable should be built in docker (make build-sandtable-in-docker)"
	cmake -B ${BUILD_DIR}/cmake-build-debug -S src
	cmake --build ${BUILD_DIR}/cmake-build-debug -j $(shell nproc)

clean-sandtable:
	rm -rf ${BUILD_DIR}/cmake-build-debug

sync-docker-files:
	scripts/docker_rsync.sh

build-sandtable-in-docker:
	docker exec controller bash -c "cd /root/sandtable && make build-sandtable"

clean-sandtable-in-docker:
	docker exec controller bash -c "cd /root/sandtable && make clean-sandtable"

config-network:
	sudo scripts/batch_config_tproxy.sh -n 20 -b docker -c controller start

unconfig-network:
	sudo scripts/batch_config_tproxy.sh -n 20 -b docker -c controller stop

start-docker: sync-docker-files
	cd docker && docker-compose up --build -d
	make build-sandtable-in-docker
	make config-network

stop-docker:
	make unconfig-network
	cd docker && docker-compose down

check_xraft_election_bug:
	docker exec controller rm -rf '/root/sandtable/systems/Xraft/specs/mc'
	docker exec controller sh -c "cd /root/sandtable/systems/Xraft/scripts && python3 /root/sandtable/scripts/tlcwrapper.py -s mc.ini"
	docker exec controller sh -c "cd /root/sandtable/systems/Xraft/specs && find -name MC.out | xargs python3 /root/sandtable/scripts/trace_reader.py | jq -c '.[].netcmd[0]'"

replay_xraft_election_bug:
	docker exec -it controller rm -rf /root/sandtable/systems/Xraft/bugs/election_safety/test
	docker exec -it controller /root/sandtable/systems/Xraft/scripts/run_one_testcase.sh /root/sandtable/systems/Xraft/bugs/election_safety/MC.out
	echo ==== Replay logs location: build/mount/systems/Xraft/bugs/election_safety/test
	grep -r "become leader, term" build/mount/systems/Xraft/bugs/election_safety/test/log*

check_xraft_kv_linearizability_bug:
	docker exec controller rm -rf '/root/sandtable/systems/Xraft-KVStore/specs/mc'
	docker exec controller sh -c "cd /root/sandtable/systems/Xraft-KVStore/scripts && python3 /root/sandtable/scripts/tlcwrapper.py -s mc.ini"
	docker exec controller sh -c "cd /root/sandtable/systems/Xraft-KVStore/specs && find -name MC.out | xargs python3 /root/sandtable/scripts/trace_reader.py | jq -c '.[].netcmd[0]'"

replay_xraft_kv_linearizability_bug:
	docker exec -it controller rm -rf /root/sandtable/systems/Xraft-KVStore/bugs/linearizability/test
	docker exec -it controller /root/sandtable/systems/Xraft-KVStore/scripts/run_one_testcase.sh /root/sandtable/systems/Xraft-KVStore/bugs/linearizability/MC.out
	echo ==== Replay logs location: build/mount/systems/Xraft-KVStore/bugs/linearizability/test

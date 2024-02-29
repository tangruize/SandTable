BUILD_DIR := .

ifeq ($(wildcard /.dockerenv),)
    # not in docker
    BUILD_DIR := build
endif

sync-docker-files:
	scripts/docker_rsync.sh

clean:
	rm -rf ${BUILD_DIR}/cmake-build-debug

clean-in-docker:
	docker exec controller bash -c "cd /root/sandtable && make clean"

build-sandtable:
	@test -f /.dockerenv || echo "Warning: SandTable should be built in docker (make build-sandtable-in-docker)"
	cmake -B ${BUILD_DIR}/cmake-build-debug -S src
	cmake --build ${BUILD_DIR}/cmake-build-debug -j $(shell nproc)

build-sandtable-in-docker:
	docker exec controller bash -c "cd /root/sandtable && make build-sandtable"

build-cpp-raft-driver:
	cmake -B ${BUILD_DIR}/cmake-build-debug/drivers -S systems/WRaft-series/driver
	cmake --build ${BUILD_DIR}/cmake-build-debug/drivers -j $(shell nproc)

build-cpp-raft-driver-in-docker:
	docker exec controller bash -c "cd /root/sandtable && make build-cpp-raft-driver"

config-network:
	sudo scripts/batch_config_tproxy.sh -n 20 -b docker -c controller start

unconfig-network:
	sudo scripts/batch_config_tproxy.sh -n 20 -b docker -c controller stop

config-network-lxd:
	sudo scripts/batch_config_tproxy.sh -n 20 -b lxc -c sandtable-lxc start

unconfig-network-lxd:
	sudo scripts/batch_config_tproxy.sh -n 20 -b lxc -c sandtable-lxc stop

build-docker:
	cd docker && docker-compose build

start-docker: sync-docker-files
	cd docker && docker-compose up -d
	make build-sandtable-in-docker
	make build-cpp-raft-driver-in-docker
	make config-network

stop-docker:
	make unconfig-network
	cd docker && docker-compose down

#### system specific targets

include systems/PySyncObj/Makefile
include systems/WRaft-series/Makefile
include systems/RaftOS/Makefile
include systems/Xraft-series/Makefile
include systems/ZooKeeper/Makefile

import asyncio

from .network import UDPProtocol
from .state import State
from .conf import config

async def register(*address_list, cluster=None, loop=None):
    """Start Raft node (server)
    Args:
        address_list — 127.0.0.1:8000 [, 127.0.0.1:8001 ...]
        cluster — [127.0.0.1:8001, 127.0.0.1:8002, ...]
        net_address_map -{'10.255.255.101:10107':'10.1.7.101:10107',...}
    """

    loop = loop or asyncio.get_event_loop()
    for address in address_list:
        host, port = address.rsplit(':', 1)
        node = Node(address=(host, int(port)), loop=loop)
        await node.start()

        for address in cluster:
            host, port = address.rsplit(':', 1)
            port = int(port)

            if (host, port) != (node.host, node.port):
                node.update_cluster((host, port))
    return node


def stop():
    for node in Node.nodes:
        node.stop()


class Node:
    """Raft Node (Server)"""

    nodes = []

    def __init__(self, address, loop):
        self.host, self.port = address
        self.cluster = set()

        self.loop = loop
        self.state = State(self)
        self.requests = asyncio.Queue(loop=self.loop)
        self.__class__.nodes.append(self)

    async def start(self):
        protocol = UDPProtocol(
            queue=self.requests,
            request_handler=self.request_handler,
            loop=self.loop
        )
        address = self.host, self.port
        self.transport, _ = await asyncio.Task(
            self.loop.create_datagram_endpoint(protocol, local_addr=address),
            loop=self.loop
        )
        self.state.start()
    
    async def keep_node_alive(self):
        """use this function to keep node alive to do other things"""
        if cls.leader is None:
            cls.leader_future = asyncio.Future(loop=self.loop)
            await cls.leader_future

    def stop(self):
        self.state.stop()
        self.transport.close()

    def update_cluster(self, address_list):
        self.cluster.update({address_list})

    @property
    def cluster_count(self):
        return len(self.cluster)

    def request_handler(self, data):
        self.state.request_handler(data)

    async def send(self, data, destination):
        """Sends data to destination Node
        Args:
            data — serializable object
            destination — <str> '127.0.0.1:8000' or <tuple> (127.0.0.1, 8000)
        """
        if isinstance(destination, tuple):
            destination=":".join("%s"%i for i in destination)
        if not config.net_address_map is None:
            masque_addr = config.net_address_map.get(destination, None)
            if not masque_addr is None:
                host, port = masque_addr.split(':')
                destination = host, int(port)
            else:
                host, port = destination.split(':')
                destination = host, int(port)
        else:
            host, port = destination.split(':')
            destination = host, int(port)
        
        print("send to:", destination)
        print("data:" , data)

        await self.requests.put({
            'data': data,
            'destination': destination
        })

    def broadcast(self, data):
        """Sends data to all Nodes in cluster (cluster list does not contain self Node)"""
        list_cluster = list(self.cluster)
        list_cluster.sort()
        for destination in list_cluster:
            asyncio.ensure_future(self.send(data, destination), loop=self.loop)

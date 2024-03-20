//
// Created by tangruize on 22-5-17.
//

#include "UdpNetwork.h"
#include "Socket.h"

#include <unistd.h>
#include <thread>
#include <sys/epoll.h>
#include <sys/sendfile.h>
#include <netinet/udp.h>
#include <chrono>

void UdpNetwork::run_epoll() {
    struct epoll_event events[max_events];
    int nfds, udp_fd = udp->socket();
    
    
    // pair<int, int> conn_fds;
    char recv_buff[1472]; // MSS: 1500(MTU)-20(IP)-8(UDP)
    // ssize_t num_read;
    while (true) {
        nfds = epoll_wait(epoll_fd, events, max_events, -1);
        if (nfds == -1) {
            if (errno == EINTR) {
                cerr_detail << "epoll_wait is interrupted by signal" << endl;
                continue;
            }
            else
                throw_syserror("epoll_wait");
        }
        for (int n = 0; n < nfds; ++n) {
            if (events[n].data.fd == udp_fd) { // udp 处理
            // udp读取到信息进行转发 
                AcceptData* client = new AcceptData; 
                wait_message(client, udp_fd, recv_buff); 
                add_msg_to_net(*client, recv_buff);
                // find one to send
                if(simple_redirect){
                    do_send(msg_counter); 
                }
            } else if(events[n].data.fd == ssh_fd){
                if (events[n].events & EPOLLIN) {
                    ssh_handle(ssh_fd);
                }
                // cout<<tcp_fd<<endl;
            }
        }
    }
}

void UdpNetwork::ssh_handle(int tcp_fd){
    struct sockaddr_in client_addr{};
    socklen_t length = sizeof(client_addr);
    int fd = accept(tcp_fd, (sockaddr *) &client_addr, &length);
    // if (fd > 0) {
    //     //设置响应事件,设置可读和边缘(ET)模式
    //     //很多人会把可写事件(EPOLLOUT)也注册了,后面会解释
    //     epev.events = EPOLLIN | EPOLLET;
    //     epev.data.fd = fd;
    //     //设置连接为非阻塞模式
    //     int flags = fcntl(fd, F_GETFL, 0);
    //     if (flags < 0) {
    //         cout << "set no block error, fd:" << fd << endl;
    //         continue;
    //     }
    //     if (fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) {
    //         cout << "set no block error, fd:" << fd << endl;
    //         continue;
    //     }
    //     //将新的连接添加到epoll中
    // }
    string node_name = configFile.get_node_name_with_addr(client_addr);
    cerr_verbose << "Client " << configFile.get_node_name_with_addr(client_addr)
                     << " cmd fd: " << fd << endl;
    client_addr.sin_port = 0;
    client_to_fd[client_addr] = fd;
    fd_to_client[fd] = client_addr;
    add_monitor_fd(fd);
    remote_control->add_node(configFile.get_node_name(client_addr), fd);
}

UdpNetwork::UdpNetwork(UdpSokcet *udp_socket) : udp(udp_socket) {
    int ssh_port = udp_socket -> bindport();
    epoll_fd = epoll_create1(0);
    if (epoll_fd == -1)
        throw_syserror("epoll_create1");
    // udp_socket 监听
    add_monitor_fd(udp_socket->socket());
    // ssh port

    this->ssh_fd = ::socket(AF_INET, SOCK_STREAM, 0);
    if (this->ssh_fd == -1)
        throw_syserror("socket");
    // if (set_nonblocking(tcp_fd) == -1)
    //     throw_syserror("set_nonblocking");
    const int opt = 1;
    struct sockaddr_in bind_addr{};
    bind_addr.sin_family = AF_INET;
    bind_addr.sin_addr.s_addr = htonl(INADDR_ANY);
//    inet_aton("127.0.0.1", &bind_addr.sin_addr);
    bind_addr.sin_port = htons(ssh_port);
    if (setsockopt(this->ssh_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt)) == -1)
        throw_syserror("setsockopt");

    cerr_verbose << "Bind ip " << inet_ntoa(bind_addr.sin_addr) << endl;
    if (bind(this->ssh_fd, (struct sockaddr*)&bind_addr, sizeof(bind_addr)) == -1)
        throw_syserror("bind");
    cerr_verbose << "ssh fd Listen on port " << ssh_port << endl;
    if (listen(this->ssh_fd, 10) < 0)
        throw_syserror("listen");
    add_monitor_fd(this->ssh_fd);

    
    if(simple_redirect){
        cerr_verbose << "simple redirect mode" <<endl;
    } else {
        cerr_verbose << "intercept mode" <<endl;
    }

    is_direct = configFile.get_strategy() == STRATEGY_DIRECT;
    flag_block = false;
}

int UdpNetwork::send_to_transparenty(const char *buf,int len,const struct sockaddr_in *source,
const struct sockaddr_in *destination){
	int fd,flags;
	fd=socket(AF_INET, SOCK_DGRAM, 0);
	flags=1;
	if (setsockopt(fd, SOL_IP,  IP_TRANSPARENT, &flags, sizeof(int)) ==-1){
		cerr_warning <<"destination-setsockopt()  IP_TRANSPARENT error!"<<endl;
		return -1;
	}else{
		//printf("destination-setsockopt IP_TRANSPARENT isOK...\n");
	}
	setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &flags, sizeof(flags));
    // todo ???
	// setsockopt(fd, SOL_SOCKET, SO_BROADCAST, &flags, sizeof(flags)); 
	if(bind (fd, (struct sockaddr *) source,sizeof(*source))==-1){
        cerr_warning <<"source-bind() error!"<<endl;
		return -1;
	}
	flags=0;
	if(sendto(fd, buf, len, flags,(struct sockaddr*)destination,sizeof(*destination))==-1){
        cerr_warning <<"destination-sendto() error!"<<endl;
		return -1;
	}

    // for detail 
    if (FLAGS_detail ) {
          cerr_detail << "Transfer msg " << configFile.get_node_name_with_addr(*source) << " -> " << configFile.get_node_name_with_addr(*destination)
           << " size: " << len << endl;
    }
	close(fd);
	return 1;
}

int UdpNetwork::wait_message(AcceptData* ret, const int udp_socket, char *data) const {
    // struct AcceptData ret{};
    ret->socket_fd = udp_socket;

	struct msghdr msg;
    struct cmsghdr *cmsg;
	struct iovec iov;
	char ctl_buf[CTL_BUF_SIZE];
    /* init buffer */
    memset(data,0,MAX_MSG);
	memset(&msg, 0, sizeof(msg));
	msg.msg_name = &ret->client_addr;
	msg.msg_namelen = sizeof(ret->client_addr);
	msg.msg_controllen = CTL_BUF_SIZE;
	msg.msg_control = ctl_buf;
	msg.msg_iovlen = 1;
	msg.msg_iov = &iov;
	iov.iov_base = data;
	iov.iov_len = MAX_MSG;
	
	int n = recvmsg(ret->socket_fd, &msg, 0);
    
    if(n<0) {	
        warn_syserror("recvmsg");
        // cerr_warning<< "no message"<<endl;
        return n;
	}
	// cerr_verbose_cont << " Get Message source "<< inet_ntoa(ret->client_addr.sin_addr)<<" :" << ntohs(ret->client_addr.sin_port);  
    // cerr_detail_cont << " Get Message source "<< configFile.get_node_name_with_addr(ret->client_addr);  

    // memset(&destinationAddr,0,sizeof(struct sockaddr_in));
	for (cmsg = CMSG_FIRSTHDR(&msg); cmsg; cmsg =CMSG_NXTHDR(&msg,cmsg)){
	  if (cmsg->cmsg_level == SOL_IP && cmsg->cmsg_type ==IP_RECVORIGADDRS){
		  memcpy(&ret->origin_addr,(struct sockaddr_in*)CMSG_DATA(cmsg),sizeof(struct sockaddr_in));
		  ret->origin_addr.sin_family = AF_INET;
          ret->masque_addr = configFile.get_masquerade_addr(ret->origin_addr);
          ret->origin_client_addr = configFile.get_origin_addr(ret->client_addr);
          // get addr 
          

            cerr_detail_cont << data<<endl;
        //   cerr_detail_cont << " destination" << configFile.get_node_name_with_addr(ret->masque_addr)<<endl;   
        //   if (configFile.is_router_addr(ret->origin_addr)) {
        //     cerr_detail_cont << endl;
        //   } else {
        //     cerr_detail_cont << " (origin: " << configFile.get_node_name_with_addr(ret->origin_addr) << ")" << endl;
        //   }
          // 这时候buf里面已经存有数据
          //send_to_transparenty(buf,n,&sourceAddr,&destinationAddr);
		  //sendto(fd,buf,n,&sourceAddr,&destinationAddr);
          return n;
	  }
	}
    return -1;
}

bool UdpNetwork::do_send(const uint32_t seq_num){
    // todo : add drop message
    if(flag_block){
        cerr_detail << "network block"<<endl;
        return true;
    }
        
    auto num_msg = network.find(seq_num);
    if(num_msg == network.end()){
        cerr_warning << "do_send cannot find message seq: " << seq_num << endl;
        throw_syserror("do_send cannot find message seq");
        return false;
    }
    UdpMsg msg = num_msg->second;
    // if (configFile.is_router_addr(*msg.get_dst())) {
    //     cerr_detail << "Transfer msg to router" << configFile.get_node_name_with_addr(*msg.get_src()) << " -> " << configFile.get_node_name_with_addr(*msg.get_dst())<<endl;
    //     string node_name = configFile.get_node_name_with_addr(*msg.get_dst());
    //     cerr_verbose << "Client " << configFile.get_node_name_with_addr(*msg.get_dst());
        
    //                  << " cmd fd: " << acc.socket_fd << endl;
    //     acc.client_addr.sin_port = 0;
    //     client_to_fd[acc.client_addr] = acc.socket_fd;
    //     fd_to_client[acc.socket_fd] = acc.client_addr;
    //     // add_monitor_fd(acc.socket_fd);
    //     remote_control->add_node(configFile.get_node_name(acc.client_addr), acc.socket_fd);
    //     // return {-2, -2};  // success, is router fd
    //     network.erase(num_msg); 
    //     return true;  
    // }
    if(send_to_transparenty(msg.buffer(), msg.size(), msg.get_src(), msg.get_dst()) == -1){
                throw_syserror("send transparently");
                network.erase(num_msg); 
                return false;
    } 
    network.erase(num_msg); 
    return true;  
}

bool UdpNetwork::do_send(const UdpMsg& msg){
    // todo : add drop message
    if(flag_block){
        cerr_detail << "network block"<<endl;
        return true;
    }
    auto num_msg = network.find(msg.get_seq());
    if(num_msg == network.end()){
        cerr_warning << "do_send cannot find message seq: " << msg.get_seq() << endl;
        return false;
    }
    if(send_to_transparenty(msg.buffer(), msg.size(), msg.get_src(), msg.get_dst()) == -1){
                throw_syserror("send transparently");
                return false;
    } 

    network.erase(num_msg); 
    return true;  
}

void UdpNetwork:: add_msg_to_net(AcceptData &client, char* data){
    msg_counter++;
    UdpMsg msg(msg_counter, data, &client.origin_client_addr, &client.masque_addr);
    network.insert(make_pair(msg_counter, msg)); 
}

void UdpNetwork:: add_msg_to_net(sockaddr_in* src, sockaddr_in* dst, char* data){
    msg_counter++;
    UdpMsg msg(msg_counter, data, src, dst);
    network.insert(make_pair(msg_counter, msg)); 
}

void UdpNetwork:: add_msg_to_net(int msg_counter, sockaddr_in* src, sockaddr_in* dst, char* data){
    UdpMsg msg(msg_counter, data, src, dst);
    network.insert(make_pair(msg_counter, msg)); 
}


void UdpNetwork::add_monitor_fd(int fd) const {
    struct epoll_event ev{};
    ev.events = EPOLLIN;// | EPOLLET;  // edge triggered
    ev.data.fd = fd;
    if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, fd, &ev) == -1)
        throw_syserror("epoll_ctl");
}

bool UdpNetwork::deliver (int msg_num){
    return do_send((uint32_t)msg_num);
}

void UdpNetwork::print_status(){
    bool showed = false;
    net_status_cache.clear();
    for (auto &msg: network) {
        msg.second.show();
        showed = true;
    }
    for (auto &msg: network) {
        net_status_cache += "msgs " + to_string(msg.first);
        net_status_cache += " : " + configFile.get_node_name_with_addr(*msg.second.get_src()) + " -> " + configFile.get_node_name_with_addr(*msg.second.get_dst());
        net_status_cache += "\n";
    }
    if (!showed)
        cerr << "(empty network buffer)" << endl;
}

void UdpNetwork::deliver_all(int least_count) {
    int count = 0;
    while (true) {
        for (auto &i: network) {
            while (do_send(i.first))
                count++;
        }
        if (count >= least_count)
            break;
        cerr_detail << "UdpNetwork::deliver_all delivered " << count << " msgs" << endl;
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
}

bool UdpNetwork::sendData(const string &src, const string &dst, char* data){
    msg_counter++;
    struct sockaddr_in src_addr = configFile.get_node_addr(src);
    struct sockaddr_in dst_addr = configFile.get_node_addr(dst);
    add_msg_to_net(msg_counter, &src_addr, &dst_addr, data);
    return do_send(msg_counter);

}

bool UdpNetwork::dropMessage(int msg_num){
    auto num_msg = network.find(msg_num);
    if(num_msg == network.end()){
        cerr_warning << "do_send cannot find message seq: " << msg_num << endl;
        return false;
    }
    network.erase(num_msg); 
    return true; 
}

bool UdpNetwork::duplicateMessage(int msg_num){
    auto num_msg = network.find(msg_num);
    msg_counter++;
   
    
    if(num_msg == network.end()){
        cerr_warning << "do_send cannot find message seq: " << msg_num << endl;
        return false;
    }
    UdpMsg msg = num_msg->second;
    msg.set_seq(msg_counter);
    network.insert(make_pair(msg_counter, msg)); 
    return true; 
    
}

void UdpNetwork::set_block(){
    flag_block = true;
}

void UdpNetwork::set_unblock(){
    flag_block = false;
}

void UdpNetwork::init(int n_servers) {
    server_count = n_servers;
    cerr_verbose << "Waiting for " << n_servers << " clients" << endl;
    for (int i = 1; ; i++) {
        if (int(client_to_fd.size()) == server_count) {
            break;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        if (i % 30 == 0) {
            cerr_detail << "Current ready " << client_to_fd.size() << " clients" << endl;
        }
    }
    cerr_detail << "Ready " << n_servers << " clients" << endl;
}

bool UdpNetwork::send_cmd(const string &node, const string &cmd, int lineno) {
    struct sockaddr_in addr = configFile.get_node_addr(node);
    cerr_detail << "Send cmd to " << configFile.get_node_name_with_addr(addr) << ": " << cmd << endl;
    int ret = remote_control->send_cmd_interceptor(node, cmd, lineno);
    if (ret < 0) {
        auto it = client_to_fd.find(addr);
        it = client_to_fd.find(addr);
        if (it == client_to_fd.end()) {
            cerr_warning << "send_cmd cannot find client-router connection: \""
                         << configFile.get_node_name_with_addr(addr) << "\"" << endl;
            return false;
        }
        close(it->second);
        // TODO: (bug) concurrent, should erase carefully
        fd_to_client.erase(it->second);
        client_to_fd.erase(it);
    }
    return ret == 0;
}

bool UdpNetwork::send_cmd_all(const string &prefix, const string &cmd, int lineno) {
    bool ok = false;
    cerr_detail << "Send cmd (" << prefix << " " << cmd << ") to all" << endl;
    for (auto &i: client_to_fd) {
        string node = configFile.get_node_name(i.first, false);
        if (!node.empty()) {
            string full_cmd = prefix;
            full_cmd += " ";
            full_cmd += cmd;
            if (0 == remote_control->send_cmd_interceptor(node, full_cmd, lineno))
                ok = true;
        }
    }
    return ok;
}


UdpNetwork* udpNet;
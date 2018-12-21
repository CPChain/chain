#!/usr/bin/env python3
import subprocess
from threading import Timer
import re
import sys
from threading import Thread, Lock
from time import sleep
import os


class Node:
    def __init__(self, number, cmd, log_file):
        self._lock = Lock()
        self._number = number
        self._log_path = log_file
        self._listeners = []

        # compose command
        self._process = subprocess.Popen(cmd.split())
        Thread(target=self.listen_loop).start()

    def running(self):
        return self._process is not None and self._process.poll() is None

    def number(self):
        return self._number

    def log_path(self):
        return self._log_path

    def subscribe_log(self, listener):
        self._lock.acquire()
        self._listeners.append(listener)
        self._lock.release()

    def listen_loop(self):
        while not os.path.exists(self._log_path):
            sleep(1)

        log_reader = open(self._log_path, "r+")
        try:
            while True:
                line = log_reader.readline()
                self._lock.acquire()
                for l in self._listeners:
                    l.notify_new_log(line)
                self._lock.release()
        finally:
            log_reader.close()

    def tail(self):
        pass


bufsize = 8192

lines = int(sys.argv[1])
fname = sys.argv[2]
fsize = os.stat(fname).st_size

iter = 0
with open(sys.argv[2]) as f:
    if bufsize > fsize:
        bufsize = fsize-1
    data = []
    while True:
        iter +=1
        f.seek(fsize-bufsize*iter)
        data.extend(f.readlines())
        if len(data) >= lines or f.tell() == 0:
            print(''.join(data[-lines:]))
            break



class BlockGenChecker(object):
    _timeout = 20
    _new_block_regex = re.compile(r"Imported.*number=(\d.)", re.M)

    def __init__(self, node):
        self._node = node
        self._timer = Timer(self._timeout, self.report_error)
        self._timer.start()
        node.subscribe_log(self)

    def notify_new_log(self, log):
        m = self._new_block_regex.search(log)
        if m is not None:
            number = m.group(1)
            print(f"New block #{number} is inserted on node #{self._node.number()}")
            if self._timer is not None:
                self._timer.cancel()
            # restart timer
            self._timer = Timer(BlockGenChecker._timeout, self.report_error)
            self._timer.start()

    def report_error(self):
        print(f"The blockchain of node #{self._node.number()} stopped growing.")
        # reset timer
        self._timer = Timer(BlockGenChecker._timeout, self.report_error)
        self._timer.start()


nodes = []

checks = []

unlocks = [
    "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a",
    "0xc05302acebd0730e3a18a058d7d1cb1204c4a092",
    "0xef3dd127de235f15ffb4fc0d71469d1339df6465",
    "0x3a18598184ef84198db90c28fdfdfdf56544f747",
    "0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e",
    "0x22a672eab2b1a3ff3ed91563205a56ca5a560e08",
    "0x7b2f052a372951d02798853e39ee56c895109992",
    "0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1",
    "0xe4d51117832e84f1d082e9fc12439b771a57e7b2",
    "0x32bd7c33bb5060a85f361caf20c0bda9075c5d51",
]

passwds = [
    "conf-dev/passwords/password",
    "conf-dev/passwords/password",
    "conf-dev/passwords/password1",
    "conf-dev/passwords/password2",
    "conf-dev/passwords/password",
    "conf-dev/passwords/password",
    "conf-dev/passwords/password",
    "conf-dev/passwords/password",
    "conf-dev/passwords/password",
    "conf-dev/passwords/password",
]

validators = "enode://9826a2f72c63eaca9b7f57b169473686f5a133dc24ffac858b4e5185a5eb60b144a414c35359585d9ea9d67f6fcca29578f9e002c89e94cc4bcc46a2b336c166@127.0.0.1:30317,\
enode://7ce9c4fee12b12affbbe769a0faaa6e256bbae3374717fb94e1fb4be308fae3795c3abae023a587d8e14b35d278bd3d10916117bb8b3f5cfa4c951c5d56eeed7@127.0.0.1:30318,\
enode://1db32421dc881357c282091960fdbd13f3635f8e3f87a953b6d9c429e53469727018bd0bb02da48acc4f1b4bec946b8f158705262b37163b4ab321a1c932d8f9@127.0.0.1:30319,\
enode://fd0f365cec4e052040151f2a4a9ba23e8592acd3cacfdc4af2e8b6dbc6fb6b25ca088151889b19729d02c48e390de9682b316db2351636fdd1ee5ea1cd32bf46@127.0.0.1:30320,"

args = "run --networkid 142 --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber "


def launch_nodes():
    print("[*] Starting bootnode")

    rundir = sys.path[0]
    subprocess.Popen(f"{rundir}/bootnode-start.sh 1 dev".split())

    cpchain = os.path.abspath("../../build/bin/cpchain")
    ipc_path_base = "data/cpc-"

    for i in range(0, 10):
        idx = i + 1
        logfile = f"data/logs/{idx}.log"
        cmd = f"""{cpchain} {args} --ipcaddr {ipc_path_base}{idx} --datadir data/data{idx}  --rpcaddr 127.0.0.1:{8500+idx} --grpcaddr 127.0.0.1:{8600+idx} \ 
        --jsonrpchttpaddr 127.0.0.1:{8700+idx} --port {30310+idx} --mine \
        --unlock {unlocks[i]} --password {passwds[i]} --logfile {logfile} 2>/dev/null
        """
        sleep(0.8)
        n = Node(idx, cmd, os.path.join(rundir, logfile))
        c = BlockGenChecker(n)
        nodes.append(n)
        checks.append(c)


if __name__ == "__main__":
    print("*" * 30 + "    Scenario Tests    " + "*" * 30)
    rundir = sys.path[0]
    runmode = 'dev'
    pwd = 'password'
    init = "%s %s" % (os.path.join(rundir, "cpchain-init.sh"), runmode, )
    print("run init", init)
    subprocess.run(init.split())

    print("launch nodes")
    launch_nodes()

    init_viewer = "%s %s" % (os.path.join(rundir, "cpchain-init-dev-viewer.sh"), runmode,)
    print("run init viewer", init_viewer)
    subprocess.run(init_viewer.split())

    start_viewr = os.path.join(rundir, "cpchain-start-dev-viewer.sh")
    print("run start viewer", start_viewr)
    subprocess.run(start_viewr)

    sleep(2)
    deploy = f"{rundir}/deploy-contracts.sh {pwd}"

    print(f"[*] deploying {deploy}")
    # smart contract deploy
    subprocess.run(f"env CPCHAIN_KEYSTORE_FILEPATH=data/data1/keystore/ {deploy}".split())

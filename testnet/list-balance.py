
from cpc_fusion import Web3

def main():
    target = ['p1', 'p2', 'p3', 'p4', 'p5', 'p6', 'ca', 'bank']
    cf = Web3(Web3.HTTPProvider(f'http://127.0.0.1:8499'))
    for i in target:
        with open(f'datadir/{i}/address', 'r') as f:
            addr = f.readline()
            addr = cf.toChecksumAddress(addr)
            balance = cf.fromWei(cf.cpc.getBalance(addr), 'ether')
            print(f'{i}({addr}) => {balance}')

if __name__ == '__main__':
    main()
# 349 - 
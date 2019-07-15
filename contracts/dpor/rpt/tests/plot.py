#!/usr/bin/env python3
import matplotlib.pyplot as plt
import numpy as np




def main():
    x=np.arange(200)
    data_path="/tmp/cpchain_data.txt"
    dets=np.loadtxt(data_path,delimiter=',')
    y=dets
    plt.scatter(x,y,alpha=0.5,marker=(9,3,30))
    plt.show()


if __name__ == '__main__':
    main()

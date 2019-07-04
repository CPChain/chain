import os
import sys

def _get_version():
    chain_path=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    list=[]
    list1=[]
    list2=[]
    tags_path=os.path.join(chain_path,'.git/refs/tags')
    for i,j,k in os.walk(tags_path):
        tag_files = k
    tag_files.remove('upstream')
    for i in tag_files:
        list.append(i.split(".")[1])
    list.sort()
    max1=list[-1]
    for i in tag_files:
        if(max1==(i.split(".")[1])and (not i.endswith('-doc'))):
            list1.append(i.split(".")[2])
    list1.sort()
    max2=list1[-1]
    for i in tag_files:
        str=i.split(".")
        if(max1==(i.split(".")[1]) and max2==i.split(".")[2] and len(str)==3):
            version="0."+max1+"."+max2
            return version
        if(max1==(i.split(".")[1]) and max2==i.split(".")[2] and len(str)==4):
            list2.append(i.split(".")[3])
    list2.sort()
    max3=list2[-1]
    version="0."+max1+"."+max2+"."+max3
    return version


def main():
    new_version=_get_version()
    sys.stderr.write(new_version)
    sys.stderr.flush()
    sys.exit(0)

if __name__ == '__main__':
    main()


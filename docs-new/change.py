import os 
import sys

# for f_name in os.walk(r'E:\chain-docs\chain\docs-new\docs'):
#     if f_name.endswith('.md'):
#         print(f_name)
filetype=".md"


for dirpath, dirNames, fileNames in os.walk(r'E:\chain-docs\chain\docs-new\docs'):
    filepathresult=[]
    for fileName in fileNames:
        apath = os.path.join(dirpath ,fileName)
        apathname = os.path.splitext(apath)[0]
        apathtype = os.path.splitext(apath)[1]
        if filetype == apathtype:
            filepathresult.append(apath)
        for i in range(len(filepathresult)):
            print(filepathresult[i])
# -*- coding:utf-8 -*-
import os
import re
import time

# 获取目录下所有交叉引用对应的标签，标题，文件名形成的字典，对应关系为标签为key，标题和文件名组成的list为value
def modify_md_content(top):
    dict_cross_referencing = {}
    for root, dirs, files in os.walk(top, topdown=False):
        # 循环文件
        for file_name in files:
            file_name_split = file_name.split('.')
 
            try:
                if file_name_split[-1] == 'rst':
                    md_file_path = os.path.join(root, '.'.join(file_name_split))
                    with open(md_file_path, 'r', encoding='utf8') as fr:
                        data = fr.read()
                        #选择md文件中想要替换的字段
                        result = re.findall(r'\.\.[ \t]\_([\S]{2,})\:',data)
                        for i in result:
                            ttt=[]
                            r_i = '.. _'+i+':'
                            search_data = re.split(r_i,data)[1]
                            result1 = re.search(r'([\S]{2,}[ \t\S]{0,})\n[\*\^\=\"\~\-\+\#]{4,}',search_data).group(1)
                            ttt.append(result1)
                            ttt.append(file_name)
                            dict_cross_referencing[i]=ttt
 
                    time.sleep(0.1)
            except FileNotFoundError as e:
                print(e)
        time.sleep(0.1)
    return dict_cross_referencing

def dist_retrun(old_file_path):
    result = modify_md_content(old_file_path)
    print(result)


if __name__ == '__main__':
    old_file_path = r'E:\chain-docs\chain\docs'
    dist_retrun(old_file_path)
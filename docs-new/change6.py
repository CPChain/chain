# -*- coding:utf-8 -*-
import os
import re
import time
 
 
def modify_md_content(top):
    ttt = os.path.relpath('E:\\chain-docs\\chain\\docs\\api\\cpc_fusion.rst','E:\\chain-docs\\chain\\docs\\cpc_faucet\\faucet.rst')
    print(ttt)
    # for root, dirs, files in os.walk(top, topdown=False):
    #     # 循环文件
    #     for file_name in files:
    #         file_name_split = file_name.split('.')
    #         # try:
    #         #     if file_name_split[-1] == 'md':
    #         #         # 找到md文件并且复制一份md文件路径
    #         md_file_path = os.path.join(root, '.'.join(file_name_split))
    #         md_rel = os.path.relpath(md_file_path,'docs')
    #         print(md_rel)
            #         copy_md_file_path = os.path.join(root, '.'.join([f'{file_name_split[0]}_copy', file_name_split[1]]))
 
            #         # 打开md文件然后进行替换
            #         with open(md_file_path, 'r', encoding='utf8') as fr, \
            #                 open(copy_md_file_path, 'w', encoding='utf8') as fw:
            #             data = fr.read()
            #             #选择md文件中想要替换的字段
            #             data = re.sub(r'\`fusion-api\`\{\.interpreted\-text[ \t]role\=\"ref\"\}', '[fusion-api](../api/cpc_fushion.md)', data)
 
            #             fw.write(data)  # 新文件一次性写入原文件内容
            #             # fw.flush()
 
            #         # 删除原文件
            #         os.remove(md_file_path)
            #         # 重命名新文件名为原文件名
            #         os.rename(copy_md_file_path, md_file_path)
            #         print(f'{md_file_path} done...')
            #         time.sleep(0.5)
            # except FileNotFoundError as e:
            #     print(e)
        # time.sleep(0.5)
 
 
if __name__ == '__main__':
    top = r'E:\chain-docs\chain\docs'
    modify_md_content(top)
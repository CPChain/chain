import os
import re
import shutil
import time
 
def copy_rst(old_file_path,new_file_path):  # 复制原有docs文件夹至新的目录下
    shutil.copytree(old_file_path,new_file_path)
    s_remove = os.path.join(new_file_path,'_build')
    shutil.rmtree(s_remove)

# 批量转换markdown 确保 pip install 了pandoc 的最新版本
def rst_to_md(file_dir):
    for root, dirs, files in os.walk(file_dir):
        for file in files:
            file_path=os.path.join(root,file)
            if os.path.splitext(file)[1] == '.rst':
                os.chdir(root)
                print("pandoc " + file + ' -o ' + os.path.splitext(file)[0] + '.md')
                os.system("pandoc -f rst+smart+gfm_auto_identifiers+ascii_identifiers -t markdown " + file + ' -o ' + os.path.splitext(file)[0] + '.md')
                os.remove(file_path) # 移出rst文件
            elif os.path.splitext(file)[1] == '.png':
                pass
            elif os.path.splitext(file)[1] == '.svg':
                pass
            else: os.remove(file_path)
# TODO 删除空文件夹

# 获取目录下所有交叉引用对应的标签，标题，文件名形成的字典，对应关系为标签为key，标题和文件名组成的list为value,将所有的表格转成代码使pandoc不对表格进行转译
def modify_rst_content(file_dir): 
    dict_c_r = {}
    for root, dirs, files in os.walk(file_dir, topdown=False):
        # 循环文件
        for file_name in files:
            file_name_split = file_name.split('.')
            try:
                if file_name_split[-1] == 'rst':
                    rst_file_path = os.path.join(root, '.'.join(file_name_split))
                    md_file_path = re.sub(r'\.rst','.md',rst_file_path)
                    copy_rst_file_path = os.path.join(root, '.'.join([f'{file_name_split[0]}_copy', file_name_split[1]]))
                    with open(rst_file_path, 'r', encoding='utf8') as fr, \
                            open(copy_rst_file_path, 'w', encoding='utf8') as fw:
                        data = fr.read()
                        # 寻找标签
                        result = re.findall(r'\.\.[ \t]\_([\S]{2,})\:',data)
                        for i in result: # 寻找从标签开始的第一个标题
                            value_list=[]
                            r_i = '.. _'+i+':'
                            search_data = re.split(r_i,data)[1]
                            title = re.search(r'([\S]{2,}[ \t\S]{0,})\n[\*\^\=\"\~\-\+\#]{4,}',search_data).group(1)
                            value_list.append(title)
                            value_list.append(md_file_path)
                            # print(i,title,md_file_path)
                            i = re.sub(r'\`','',i)  # 标签被``包括时，去除``
                            i = i.lower()
                            dict_c_r[i]=value_list
                        # 查找所有表格，将其变成代码使pandoc不进行表格转译
                        data = re.sub(r'\n\n\+\-{5}','\n\n.. code-block:: table\n\t+-----',data) 
                        data = re.sub(r'([\+\|])\n([\|\+])',r'\1\n\t\2',data)
                        fw.write(data)  # 新文件一次性写入原文件内容
                        # fw.flush()
 
                    # 删除原文件
                    os.remove(rst_file_path)
                    # 重命名新文件名为原文件名
                    os.rename(copy_rst_file_path, rst_file_path)
                    print(f'{rst_file_path} done...')
                    time.sleep(0.1)
            except FileNotFoundError as e:
                print(e)
        time.sleep(0.1)
    return dict_c_r

def modify_md_content(filedir,dict_c_r):
    for root, dirs, files in os.walk(filedir, topdown=False):
        # 循环文件
        for file_name in files:
            file_name_split = file_name.split('.')
 
            try:
                if file_name_split[-1] == 'md':
                    # 找到md文件并且复制一份md文件路径
                    md_file_path = os.path.join(root, '.'.join(file_name_split))
                    copy_md_file_path = os.path.join(root, '.'.join([f'{file_name_split[0]}_copy', file_name_split[1]]))
 
                    def convert(value):  # 返回标题和相对路径组成的字符串
                        r_str = value.group(1).lower()
                        r_find = dict_c_r[r_str] # 从字典中获取对应值
                        r_title = r_find[0]
                        r_path = r_find[1]
                        path1 = re.split(r'[\\]{1,}',md_file_path) # 分割路径
                        path2 = re.split(r'[\\]{1,}',r_path)
                        i = 0
                        while i < len(path1): # 对比路径
                            if path1[i] == path2[i]:
                                i= i+1
                            else:
                                break
                        j = len(path1)-i-1 # 判断是否为最底层
                        k = len(path2)-i-1
                        if j == 0:
                            result1 = './'
                        else:
                            result1 = '../'*j
                        if k == 0:
                            result2 = path2[i]
                        else:
                            result2 = '/'.join(path2[i:])
                        result = '[' + r_title +']' +'(' +result1 + result2 + ')'
                        return result
                    
                    # 打开md文件然后进行替换
                    with open(md_file_path, 'r', encoding='utf8') as fr, \
                            open(copy_md_file_path, 'w', encoding='utf8') as fw:
                        data = fr.read()
                        #选择md文件中想要替换的字段
                        data = re.sub(r'::: \{\.note\}\n::: \{\.title\}\nNote\n:::', '::: tip', data) # tip替换
                        data = re.sub(r'::: \{\.warning\}\n::: \{\.title\}\nWarning\n:::', '::: warning', data)
                        try:
                            data = re.sub(r'\`([\w\-]{1,})\`\{\.interpreted\-text[ \t]role\=\"ref\"\}',convert,data) # 交叉引用替换
                        except Exception as e:
                            print('------||||||',e)
                        fw.write(data)  # 新文件一次性写入原文件内容
                        # fw.flush()
 
                    # 删除原文件
                    os.remove(md_file_path)
                    # 重命名新文件名为原文件名
                    os.rename(copy_md_file_path, md_file_path)
                    print(f'{md_file_path} done...')
                    time.sleep(0.5)
            except FileNotFoundError as e:
                print(e)
        time.sleep(0.5)


def all_change(old,new):
    try:
        copy_rst(old,new)
        time.sleep(0.5)
        print('----------------------->>>>>>>>>>>>>>>>1')
        dict_c_r = modify_rst_content(new)
        time.sleep(0.5)
        print('----------------------->>>>>>>>>>>>>>>>2')
        rst_to_md(new)
        time.sleep(0.5)
        print('----------------------->>>>>>>>>>>>>>>>3')
        modify_md_content(new,dict_c_r)
        print('----------------------->>>>>>>>>>>>>>>>4')
    except Exception as e:
        print(e)


if __name__ == '__main__':
    old = r'E:\chain-docs\chain\docs'
    new = r'E:\chain-docs\chain\docs-new\docs\content'
    all_change(old,new)
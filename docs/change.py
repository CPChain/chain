import os
import re
import shutil
import time
 
def rm_exists_files(exist_file_path):
    if os.path.exists(exist_file_path):
        shutil.rmtree(exist_file_path)
        print(exist_file_path)


def copy_rst(old_file_path,new_file_path):  # 复制原有docs文件夹至新的目录下
    shutil.copytree(old_file_path,new_file_path,ignore=shutil.ignore_patterns("_build"))

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

                    def convert1(value):  
                            r_str_1 = value.group(1)
                            r_str_2 = value.group(3)
                            r_len = len(r_str_1)+len(r_str_2) + 10
                            result = '\n' +'`class` '+ r_str_1 + '.'+ r_str_2 +'\n' + '+'*r_len +'\n'
                            return result
                    def convert2(value):  
                            r_str_1 = value.group(1)
                            r_len = len(r_str_1) + 10
                            result = '\n' +'`class` '+ r_str_1  +'\n' + '+'*r_len +'\n'
                            return result
                    with open(rst_file_path, 'r', encoding='utf8') as fr, \
                            open(copy_rst_file_path, 'w', encoding='utf8') as fw:
                        data = fr.read()
                        # 寻找标签
                        result = re.findall(r'\.\.[ \t]\_([\S]{2,})\:\n',data)
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
                        data = re.sub(r'\.\.[ \t]py\:module\:\:[ \t]([\S \t]{3,})\n(\.\.[ \t]py\:currentmodule\:\:[ \t][\S \t]{3,}\n)?\n\.\.[ \t]py\:class\:\:[ \t]([\S \t]{3,})\n',convert1,data)
                        data = re.sub(r'\.\.[ \t]py\:[\w]{4,}\:\:[ \t]([\S \t]{3,})\n',convert2,data) # sphinx 内置Python方法转换
                        data = re.sub(r'\.\.[ \t]index\:\:[\S \t]{1,}\n','',data) # 删除索引
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
                        r_str_1 = value.group(1).lower()
                        r_str_2 = value.group(2)
                        if r_str_2 == None:
                            r_str = r_str_1
                            r_find = dict_c_r.get(r_str,None) # 从字典中获取对应值
                            if r_find == None:
                                return '------>>>>>>' + r_str
                            r_title = r_find[0]
                            r_path = r_find[1]
                        else:
                            r_str_2 = re.sub(r'\<([\w\-]{1,})\>',r'\1',r_str_2)
                            r_str = r_str_2.lower()
                            r_find = dict_c_r.get(r_str,None) # 从字典中获取对应值
                            if r_find == None:
                                return '------>>>>>>' + r_str
                            r_title = r_str_1
                            r_path = r_find[1]
                        path1 = re.split(r'[\\]{1,}',md_file_path) # 分割路径
                        path2 = re.split(r'[\\]{1,}',r_path)
                        anchor = re.sub(r'[ \t\_\.\/\(\)]','-',r_title) # 转换标题为对应锚点
                        anchor = re.sub(r'\-{2,}','-',anchor).lower() 
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
                        elif j == -1:
                            result1 = ''
                        else:
                            result1 = '../'*j
                        if k == 0:
                            result2 = path2[i]
                        elif k == -1:
                            result2 = ''
                        else:
                            result2 = '/'.join(path2[i:])
                        result = '[' + r_title +']' +'(' + result1 + result2 + '#' + anchor + ')'
                        return result


                    def convert_table(value):
                        matched = '\n'+ value.group(1) +'\n' # 获取表格
                        matched = re.sub(r'([^\-\n\=])\+([^\-\n\=])',r'\1need_to_change_at_end\2',matched)
                        Table = re.split(r'\n\+[\=\+]{5,}\n',matched) # 分割表头表内容
                        if len(Table) == 2: # 判断有无表头
                            Th = Table[0] # 表头
                            Td = Table[1] # 表内容
                            Th_rows = re.split(r'\n\+[\+\-]{5,}\n',Th) # 分割成row
                            Th_rows = Th_rows[1:] # 去除为空的第一项
                            Th_row_list = []
                            Th_row_list_len = [] # 表头 row 里的列数
                            Td_row_list = []  # 表格内容 里所有row的集合
                            Td_rows = re.split(r'\n\+[\+\-]{5,}\n',Td)  # 分割成大行row
                            Td_rows = Td_rows[:-1] # 去除为空的最后一项
                            for row in Th_rows:
                                col_list = re.split(r'\|',row)
                                col_list = col_list[1:-1]
                                Th_row_list_len.append(len(col_list))

                            for j in range(0,len(Th_rows)):
                                col_list = re.split(r'\|',Th_rows[j])
                                col_list = col_list[1:-1]
                                col_colspan = str(int(max(Th_row_list_len)/Th_row_list_len[j]))
                                for k in range(0,len(col_list)):
                                    col_list[k] ='<th colspan="' + col_colspan + '">' + col_list[k] +'</th>'
                                Th_row_tr = '<tr>\n\t\t' + '\n\t\t'.join(col_list) + '\n\t</tr>'
                                Th_row_list.append(Th_row_tr)
                            Th_row_all = '\n\t'.join(Th_row_list)

                        elif len(Table) == 1:
                            Td = Table[0]
                            Th_row_all = ''
                            Td_row_list = []  # 表格内容 里所有row的集合
                            Td_rows = re.split(r'\n\+[\+\-]{5,}\n',Td)  # 分割成大行row
                            Td_rows = Td_rows[1:-1] # 去除为空的最后一项

                        for row in Td_rows: # 对每个row进行处理
                            # print(row)
                            row_col_list = []  # row 的 col 的集合
                            row_col_list_len = [] # row 里 每一列 的行数

                            Td_row_tr_list = [] # 表格内容 里每一行的所有tr的集合
                            line_list = re.split(r'\n',row) # 按换行切割row为line
                            # print(lines)
                            i = 0
                            while i < len(line_list):
                                line_col_list = re.split(r'[\|\+]',line_list[i]) # 根据 | 或者 + 分割每一个 line 成col ，之后组合每一line的col ，即每一大行里的每一列合成为一个字符串
                                if i == 0:
                                    for j in range(0,len(line_col_list)):
                                        row_col_list.append(line_col_list[j])
                                else:
                                    for j in range(0,len(line_col_list)):
                                        row_col_list[j]= row_col_list[j] + line_col_list[j]
                                i = i + 1
                            row_col_list = row_col_list[1:-1] # 去除空值
                            for j in range(0,len(row_col_list)):
                                row_col_list[j]=re.sub(r'[ \t]{2,}',' ',row_col_list[j])
                                row_col_list[j]=re.split(r'\-{4,}',row_col_list[j]) # 对每一列按照'--------'进行分割
                                row_col_list_len.append(len(row_col_list[j])) # 记录每一列的行数
                            


                            for t in range(0,max(row_col_list_len)):
                                Td_row_tr_td_list =[]
                                for j in range(0,len(row_col_list)):
                                    if t < row_col_list_len[j]:
                                        Td_row_tr_td_rowspan = str(int((max(row_col_list_len))/row_col_list_len[j])) # 每一个 td 里的rowspan的值
                                        Td_row_tr_td ='<td  rowspan="'+ Td_row_tr_td_rowspan + '">' + row_col_list[j][t] + '</td>' # 合成每一个td
                                        Td_row_tr_td_list.append(Td_row_tr_td) 
                                    else:
                                        pass
                                Td_row_tr_list.append(Td_row_tr_td_list)
                            for h in range(0,len(Td_row_tr_list)): 
                                Td_row_tr_list[h]= '\n\t\t'.join(Td_row_tr_list[h]) # 每一个tr里的td join成一个字符串
                                Td_row_tr_list[h]= '<tr>\n\t\t'+ Td_row_tr_list[h] + '\n\t</tr>' # 合成每一个tr
                                            
                            Td_row_tr_all = '\n\t'.join(Td_row_tr_list) # 每一行所有的tr合成为一个字符串
                            Td_row_list.append(Td_row_tr_all)
                        Td_row_all = '\n\t'.join(Td_row_list) # 所有的row,join成一个字符串
                        result_start = '<table cellspacing="0" cellpadding="5">\n\t'
                        result_end = '\n</table>'
                        result = result_start + Th_row_all + '\n\t' + Td_row_all + result_end
                        result = re.sub(r'need\_to\_change\_at\_end','+',result)
                        result = re.sub(r'\`\`([^\`\n]{2,}?)\`\`',r'<code>\1</code>',result)
                        return result

                    def convert_extra(value):
                        matched = value.group(1)
                        if matched == 'cpc_fusion.cpc':
                            return '[CPC](#class-cpc-fusion-cpc-cpc)'
                        else:
                            title = re.sub(r'cpc\_fusion\.cpc\.','',matched)
                            anchor = re.sub(r'\.',r'-',title)
                            anchor = re.sub(r'\(\)','',anchor).lower()
                            return '[' + title +'](#' + anchor + ')'



                    # 打开md文件然后进行替换
                    with open(md_file_path, 'r', encoding='utf8') as fr, \
                            open(copy_md_file_path, 'w', encoding='utf8') as fw:
                        data = fr.read()
                        #选择md文件中想要替换的字段
                        data = re.sub(r'(\>[ \t])?::: \{\.note\}\n(\>[ \t])?::: \{\.title\}\n(\>[ \t])?Note\n(\>[ \t])?:::', r'\1::: tip', data) # tip替换
                        data = re.sub(r'::: \{\.warning\}\n::: \{\.title\}\nWarning\n:::', '::: warning', data)
                        data = re.sub(r'\!\[image\]\(','![image](./',data) # 考虑为非[image]标记的图片
                        data = re.sub(r'\[([\w\-]{2,})\]\{\.title\-ref\}',r'*\1*',data)
                        data = re.sub(r'\{\#([\w\-]{2,})\}','',data)
                        data = re.sub(r'\#\#\#[ \t]\*class\*','#### *class*',data)
                        try:
                            data= re.sub(r'\`([\w\- \t\'\"\(\)]{1,}\n?[\w\- \t\'\"\(\)]{0,})(\<[\w\-]{1,}\>)?\`\{\.inte[\S \t]{0,}\n?[\S \t]{0,}ref\"\}',convert,data)
                            data= re.sub(r'\`\~([\w\- \t\.\(\)]{1,})\`\{\.interpreted-text[ \t]role="[\w]{2,}"}',convert_extra,data)
                            data = re.sub(r'\`\`\`[ \t]\{\.table\n([\S\n \t]{1,}?)\}\n\`\`\`',convert_table,data)
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

def move_md(old_file_path,new_file_path):  # 复制原有docs文件夹至新的目录下
    shutil.move(old_file_path,new_file_path)


def all_change(old,new):
    try:
        rm_exists_files(new)
        rm_exists_files(os.path.abspath(os.path.join(new,"../solidity")))
        rm_exists_files(os.path.abspath(os.path.join(new,"../zh/content")))
        rm_exists_files(os.path.abspath(os.path.join(new,"../zh/solidity")))
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
        time.sleep(0.5)
        print('----------------------->>>>>>>>>>>>>>>>4')
        shutil.move(os.path.abspath(os.path.join(new,"solidity")),os.path.abspath(os.path.join(new,"..")))
        time.sleep(0.5)
        print('----------------------->>>>>>>>>>>>>>>>5')
        shutil.copytree(new,os.path.abspath(os.path.join(new,"../zh/content")))
        time.sleep(0.5)
        print('----------------------->>>>>>>>>>>>>>>>6')
        shutil.copytree(os.path.abspath(os.path.join(new,"../solidity")),os.path.abspath(os.path.join(new,"../zh/solidity")))
        time.sleep(0.5)
        print('----------------------->>>>>>>>>>>>>>>>7')
    except Exception as e:
        print(e)


if __name__ == '__main__':
    new = os.path.abspath(os.path.join(os.getcwd(),"docs/content"))
    old = os.path.abspath(os.path.join(os.getcwd(), "../docs"))
    all_change(old,new)
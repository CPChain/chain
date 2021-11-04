import re

# A = '123123123456'
# B = '1111222233334444'
# C = 'search more'
# D = 'E:\\chain-docs\\chain\\\\docs-new\\docs\content\\solidity\docs\\\contracts.rst'
# # def change(xxx):
# #     zzz = xxx +'----'
# #     return zzz
# # result = re.sub(r'([\S]{1,})[ \t]([\S]{1,})',change(r'\1'),C)
# result = re.split(r'[\\]{1,}',D)
# print(result)
dict_c_r ={'fusion-api': ['Fusion API', 'E:\\chain-docs\\chain\\docs-new\\docs\\content\\api\\cpc_fusion.md'], 'fusion-api-using': ['Using Fusion', 'E:\\chain-docs\\chain\\docs-new\\docs\\content\\api\\cpc_fusion.md']}

data = '`fusion-api`{.interpreted-text role="ref"}xxxxxxxxxxx'


md_file_path ='E:\\chain-docs\\chain\\docs-new\\docs\\content\\solidity\\docs\\control-structures.md'

def convert(value):
    r_str = value.group(1)
    ttt = dict_c_r[r_str]
    ttt_title = ttt[0]
    ttt_path = ttt[1]
    path1 = re.split(r'[\\]{1,}',md_file_path)
    path2 = re.split(r'[\\]{1,}',ttt_path)
    i = 0
    while i <= len(path1):
        if path1[i] == path2[i]:
            i= i+1
        else:
            break
    j = len(path1)-i-1
    k = len(path2)-i-1
    if j == 0:
        result1 = './'
    else:
        result1 = '../'*j
    if k == 0:
        result2 = path2[i,]
    else:
        result2 = '/'.join(path2[i:])
    result = '[' + ttt_title +']' +'(' +result1 + result2 + ')'
    return result

data = re.sub(r'\`([\w\-]{1,})\`\{\.interpreted\-text[ \t]role\=\"ref\"\}',convert,data)
print(data)
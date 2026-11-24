"""Use one scope per component of a dotted Lean section or namespace name."""
import re
PART=re.compile(r'(?:«[^»]*»|[^.«»]+)+')
def components(name):return PART.findall(name) if name else [None]
def open_scopes(lines,clump):
    stack=[];depth=0
    for line in lines:
        if depth==0 and line and not line.startswith(('/-',' ','\t')):
            match=clump.SECTION_RE.match(line)
            if match:stack.extend(('section',n) for n in components(match.group(1)))
            else:
                match=clump.NAMESPACE_RE.match(line)
                if match:stack.extend(('namespace',n) for n in components(match.group(1)))
                elif clump.MUTUAL_RE.match(line):stack.append(('mutual',None))
                else:
                    match=clump.END_RE.match(line)
                    if match and stack:del stack[-len(components(match.group(1))):]
        depth=max(0,depth+line.count('/-')-line.count('-/'))
    return stack
def close_scopes(stack,auto):
    tail=[];result=[]
    for kind,name in reversed(stack):
        if kind=='mutual':raise ValueError('unterminated mutual block')
        if name is not None:tail.append(name);continue
        if tail:result.append('end '+'.'.join(reversed(tail))+auto);tail=[]
        result.append('end'+auto)
    if tail:result.append('end '+'.'.join(reversed(tail))+auto)
    return result

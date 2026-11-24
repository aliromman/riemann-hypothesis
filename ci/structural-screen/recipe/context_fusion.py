"""Test whether the generated scope commands themselves can meet the second target."""
import collections,itertools,re
from compact_scope import AUTO,PUB,PUBNC,WORD_END,NAMED_END
PARSED_OPEN=re.compile(r'open (?:scoped )?(?:[A-Za-z_\u0080-\uffff][\w\'.\u0080-\uffff]*)(?: +[A-Za-z_\u0080-\uffff][\w\'.\u0080-\uffff]*)*\Z')
SETUP=re.compile(r"^(?:open(?: scoped)? [\w. ']+|namespace [\w.']+|universe[s]? [\w ']+|variable[s]? [^\n]+|attribute \[local (?:instance|simp)\] [^\n]+|set_option [\w.]+ (?:true|false|\d+))$")
ANON=re.compile(r'^(?:@\[expose\] )?(?:(?:public|private|noncomputable|meta) )*section\s*(?:--.*)?$')
NAMED=re.compile(r"^end +[A-Za-z_\u0080-\uffff][\w.‘’'\u0080-\uffff]*\s*(?:--.*)?$")
PLAIN_END=re.compile(r'^end\s*(?:--.*)?$')
def match_anon(lines,start):
    depth=1
    for j in range(start+1,len(lines)):
        s=lines[j]
        if not s.strip():continue
        # An atypical scope command needs a full parser; keep its original form.
        if ANON.fullmatch(s):depth+=1
        elif PLAIN_END.fullmatch(s):
            depth-=1
            if depth==0:return j
        elif WORD_END.search(s) and not NAMED.fullmatch(s):return -1
    return len(lines)
def at_end(lines,pos):
    return pos>=0 and all(not l.strip() or PLAIN_END.fullmatch(l) or NAMED.fullmatch(l) for l in lines[pos+1:])
def fuse(lines):
    if not lines or lines[0]!=PUB or 'noncomputable section' not in lines:return lines,0
    i=lines.index('noncomputable section')
    if any(s.strip() and not SETUP.fullmatch(s) for s in lines[1:i]):return lines,0
    end=match_anon(lines,i)
    if not at_end(lines,end):return lines,0
    if any(('"' in line or '/-' in line or '-/' in line or '`' in line) for line in lines if ANON.fullmatch(line) or PLAIN_END.fullmatch(line)):return lines,0
    excluded={i,end};new=[PUBNC]+[s for j,s in enumerate(lines[1:],1) if j not in excluded]
    return new,1+(end<len(lines))
def shared_opens(bodies):
    if not bodies or any(not b or b[0] not in (PUB,PUBNC) for b in bodies):return []
    upto=min(map(len,bodies));last=0
    for i in range(1,upto):
        line=bodies[0][i]
        if any(b[i]!=line for b in bodies[1:]):break
        if not line.strip():continue
        if not PARSED_OPEN.fullmatch(line) or ' in' in line.split('--')[0]:break
        last=i
    return bodies[0][1:last+1]

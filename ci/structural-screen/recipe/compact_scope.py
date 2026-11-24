"""Explore readable, lossless boundaries for the clumps already in upstream."""
import collections,json,re
TAG='-- clump member: '
HEADER='-- clump-header: '
BEGIN='-- ===== clump member: '
END='-- ===== end clump member: '
AUTO=' -- clump:auto'
PUB='@[expose] public section'
PUBNC='@[expose] public noncomputable section'
WORD_END=re.compile(r'\bend\b')
NAMED_END=re.compile(r"end [A-Z][\w'.]*(?:\s*--.*)?\Z")
def member_start(line):
    code,sep,tag=line.partition(TAG)
    if sep and code in ('','section ',PUB+' ',PUBNC+' '):
        return code.rstrip(),tag
def own_scope(lines):
    if not lines or lines[0] not in (PUB,PUBNC):return False
    # Only a nameless end can close an anonymous section. Keep the wrapper for
    # other spellings, including potential commands in quotations.
    return all(NAMED_END.fullmatch(l) for l in lines if WORD_END.search(l))
def compact(text):
    lines=text.split('\n')
    starts=[i for i,l in enumerate(lines) if l.startswith(BEGIN)]
    if not starts:return None
    prefix=lines[:starts[0]]
    dst=list(prefix);arch=[];st=collections.Counter(files=1)
    for j,i in enumerate(starts):
        limit=starts[j+1] if j+1<len(starts) else len(lines)
        label=lines[i][len(BEGIN):-len(' =====')]
        if i+3>=limit or lines[i]!=BEGIN+label+' =====' or not lines[i+1].startswith(HEADER) or lines[i+2]!='section'+AUTO:return None
        info=json.loads(lines[i+1][len(HEADER):]);marker=END+label+' ====='
        if info.get('m')!=label:return None
        if marker not in lines[i+3:limit]:return None
        end=lines.index(marker,i+3,limit)
        if any(l.strip() for l in lines[end+1:limit]):return None
        block=lines[i+3:end];z=len(block)
        while z and block[z-1].endswith(AUTO):z-=1
        bod=block[:z];closers=block[z:]
        if not closers or closers[-1]!='end'+AUTO or any(not x.startswith('end') for x in closers):return None
        if any(l.endswith(AUTO) or l.startswith(HEADER) or member_start(l) for l in bod):return None
        last=j+1==len(starts);borrow=own_scope(bod)
        if borrow and not any(x=='end'+AUTO for x in closers[:-1]):return None
        st['members']+=1
        if (last or borrow) and bod and bod[0] in (PUB,PUBNC):
            dst.append(bod[0]+' '+TAG+label);dst.extend(bod[1:])
        elif last:dst.append(TAG+label);dst.extend(bod)
        else:dst.append('section '+TAG+label);dst.extend(bod)
        if not last:dst.extend(closers[:-1] if borrow else closers)
        if last:st['scope_commands_removed']+=1+len(closers)
        elif borrow:st['scope_commands_removed']+=2
        st['borrowed']+=not last and borrow
        dst.append('');arch.append(lines[i+1])
    return '\n'.join(dst+arch+['']),st
def recover(text):
    lines=text.split('\n');positions=[(i,*start) for i,l in enumerate(lines) if (start:=member_start(l))]
    if not positions:return None
    foot=next(i for i,l in enumerate(lines) if l.startswith(HEADER))
    names=[name for _,_,name in positions]
    infos=[]
    for line in lines[foot:]:
        if not line.strip():continue
        if not line.startswith(HEADER):raise ValueError('content after archived headers')
        infos.append(json.loads(line[len(HEADER):]))
    if names!=[i['m'] for i in infos] or len(set(names))!=len(names):raise ValueError('archived headers and sections disagree')
    result={}
    for j,(start,op,name) in enumerate(positions):
        end=positions[j+1][0] if j+1<len(positions) else foot
        if lines[end-1]!='':raise ValueError('missing member separator '+name)
        data=lines[start+1:end-1]
        while data and data[-1].endswith(AUTO):data.pop()
        if op and op!='section':data.insert(0,op)
        info=infos[j];result[name]=info['h']+'\n'.join(data)+('' if info.get('nonl') else '\n')
    return result

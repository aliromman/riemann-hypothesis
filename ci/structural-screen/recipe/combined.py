"""Generate and check compact scopes and shared opens against the existing member sources."""
import collections,json,re
from compact_scope import AUTO,BEGIN,END,HEADER,PUB,PUBNC,TAG,member_start,own_scope
from context_fusion import fuse
from share_intervals import sharing
from lean_scopes import open_scopes,close_scopes
START='-- clump: shared namespace opens'
FINISH='end -- clump: shared namespace opens'
def extract_legacy(text):
    lines=text.split('\n');starts=[i for i,l in enumerate(lines) if l.startswith(BEGIN)]
    if not starts:return None
    members=[]
    for j,i in enumerate(starts):
        limit=starts[j+1] if j+1<len(starts) else len(lines)
        if i+3>=limit or not lines[i+1].startswith(HEADER) or lines[i+2]!='section'+AUTO:return None
        info=json.loads(lines[i+1][len(HEADER):]);name=info['m'];endmark=END+name+' ====='
        if lines[i]!=BEGIN+name+' =====' or endmark not in lines[i+3:limit]:return None
        k=lines.index(endmark,i+3,limit)
        if any(l.strip() for l in lines[k+1:limit]):return None
        b=lines[i+3:k];z=len(b)
        while z and b[z-1].endswith(AUTO):z-=1
        body,close=b[:z],b[z:]
        if not close or close[-1]!='end'+AUTO or any(not x.startswith('end') for x in close):return None
        if any(l.endswith(AUTO) or l.startswith(HEADER) or member_start(l) or l in [START,'section '+START,FINISH] for l in body):return None
        members.append((name,info,body,close))
    return lines[:starts[0]],members
def render_members(prefix,names,infos,bodies,closers):
    groups=sharing(bodies);beg={a:(b,pre,benefit) for a,b,pre,benefit in groups}
    end={b for _,b,_,_ in groups if b+1!=len(names)};opens=();out=list(prefix);stats=collections.Counter()
    for i,(name,body,cs) in enumerate(zip(names,bodies,closers)):
        last=i+1==len(names)
        if i in beg:
            stop,opens,benefit=beg[i]
            out.append(START if stop+1==len(names) else 'section '+START);out.extend(opens);out.append('')
            stats['hoisted_open_gain']+=benefit;stats['groups']+=1
        use=list(body)
        if opens:
            if tuple(use[1:1+len(opens)])!=opens:raise ValueError('different leading opens '+name)
            del use[1:1+len(opens)]
        borrow=own_scope(use) and 'end'+AUTO in cs
        if (last or borrow) and use and use[0] in (PUB,PUBNC):
            out.append(use[0]+' '+TAG+name);out.extend(use[1:])
        elif last:out.append(TAG+name);out.extend(use)
        else:out.append('section '+TAG+name);out.extend(use)
        if not last:out.extend(cs);out.extend([] if borrow else ['end'+AUTO])
        out.append('')
        if i in end:out.extend([FINISH,'']);opens=()
        stats['borrowed']+=not last and borrow
    out.extend(HEADER+json.dumps(info,ensure_ascii=False) for info in infos);out.append('')
    return '\n'.join(out),stats
def modern_decode(text):
    lines=text.split('\n');markers=[]
    for i,l in enumerate(lines):
        if l.startswith(HEADER):foot=i;break
        begin=member_start(l)
        if begin:markers.append((i,'member',begin))
        elif l in (START,'section '+START):markers.append((i,'open',None))
        elif l==FINISH:markers.append((i,'close',None))
    else:raise ValueError('missing header table')
    headers=[json.loads(l[len(HEADER):]) for l in lines[foot:] if l.startswith(HEADER)]
    if any(l and not l.startswith(HEADER) for l in lines[foot:]):raise ValueError('unexpected text in the header table')
    found=[m for _,key,v in markers if key=='member' for _,m in [v]]
    if found!=[h['m'] for h in headers] or len(set(found))!=len(found):raise ValueError('member order differs from header table')
    infos={h['m']:h for h in headers};res={};opened=[]
    for j,(start,kind,v) in enumerate(markers):
        stop=markers[j+1][0] if j+1<len(markers) else foot
        if lines[stop-1]!='':raise ValueError(('missing separator',kind,str(v)))
        body=lines[start+1:stop-1]
        if kind=='open':opened=body
        elif kind=='close':
            if body or not opened:raise ValueError('unexpected group end')
            opened=[]
        else:
            op,m=v
            while body and body[-1].endswith(AUTO):body.pop()
            if op and op!='section':body.insert(0,op)
            if opened:
                if body[0] not in (PUB,PUBNC):raise ValueError('unexpected group opener '+m)
                body[1:1]=opened
            inf=infos[m];res[m]=inf['h']+'\n'.join(body)+('' if inf.get('nonl') else '\n')
    return res
def live_counts(text):
    # Marker comments attached to real commands still contribute one real command.
    ls=text.splitlines()
    return sum(bool(l.strip()) for l in ls),sum(bool(l.strip()) and not l.lstrip().startswith('--') for l in ls)
def convert(text,clump):
    extracted=extract_legacy(text)
    if not extracted:return None
    prefix,mem=extracted;names=[];infos=[];bodies=[];closing=[];expect={};s=collections.Counter()
    for n,info,body,close in mem:
        new,num=fuse(body);old_stack=clump.closers(clump.open_scopes('\n'.join(body)))
        if old_stack!=close[:-1]:return None
        closers=close_scopes(open_scopes(new,clump),AUTO)
        names.append(n);infos.append(info);bodies.append(new);closing.append(closers)
        expect[n]=info['h']+'\n'.join(new)+('' if info.get('nonl') else '\n');s['fusions']+=bool(num)
    after,details=render_members(prefix,names,infos,bodies,closing)
    if modern_decode(after)!=expect:raise ValueError('incorrect historical reconstruction')
    s.update(details);before_nb,before_code=live_counts(text);after_nb,after_code=live_counts(after)
    s.update(net=before_nb-after_nb,code=before_code-after_code,bytes=len(text.encode())-len(after.encode()),members=len(names),files=1,header_bytes=sum(len((HEADER+json.dumps(info,ensure_ascii=False)).encode()) for info in infos))
    return after,s

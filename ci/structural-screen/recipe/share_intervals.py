"""Find consecutive members whose common namespace opens pay for a real section."""
from context_fusion import PARSED_OPEN,PUB,PUBNC
def leading(body):
    if not body or body[0] not in (PUB,PUBNC):return ()
    result=[]
    for line in body[1:]:
        if line.strip() and (not PARSED_OPEN.fullmatch(line) or 'in' in line.split()):break
        result.append(line)
    while result and not result[-1].strip():result.pop()
    return tuple(result)
def common_lines(a,b):
    count=0
    for before,after in zip(a,b):
        if before!=after:break
        count+=1
    while count and not a[count-1].strip():count-=1
    return a[:count]
def sharing(bodies):
    n=len(bodies);prefix=list(map(leading,bodies));best=[0]*(n+1);choice=[None]*n
    for i in range(n-1,-1,-1):
        best[i]=best[i+1];seq=prefix[i]
        for j in range(i+1,n):
            seq=common_lines(seq,prefix[j])
            if not seq:break
            commands=sum(bool(l.strip()) for l in seq)
            never_leaks=j==n-1
            gain=(j-i)*commands-(0 if never_leaks else 2)
            if gain>0 and gain+best[j+1]>best[i]:
                best[i]=gain+best[j+1];choice[i]=(j,seq,gain)
    groups=[];i=0
    while i<n:
        if choice[i] is None:i+=1;continue
        j,seq,gain=choice[i];groups.append((i,j,seq,gain));i=j+1
    return groups

/* Tonos · Song map: a loop recorder and a chord history in one block.

   It records what the player plays (notes, timing, velocity, pedal), finds the bars and the four-bar phrases, and draws the
   take as a map at three levels of detail: Notes, Chords (the chord history) and Form (A, B, A′). It has a metronome
   tied to the selected scale, a library kept in this browser (IndexedDB), playback through the board's sound,
   bar selection + loop, MIDI-file export for Ableton, and "Use as progression".

   Integration (three touches in the page):
     1. <script src="songmap.js"></script>
     2. <section class="panel" data-blk="songmap"></section>          (plus its entry in LAY_DEF)
     3. SongMap.init({el, key:()=>key, scale:()=>scale||key, master:()=>master, CHORDS, SYM, MODE_OFFSET, LPC,
                      useProgression:p=>{…}});
        and feed it the events:  SongMap.noteOn(m,v) · SongMap.noteOff(m) · SongMap.pedal(on) · SongMap.allOff()
        and tell it when the scale changes:  SongMap.refresh()
   Everything else it needs (detectChord, spellPc, romanFor, parseDeg, tone, ac, optToggle) it takes from the page's
   own functions, so chords are named and coloured exactly like the rest of the board. */
(function(){
'use strict';
const VERSION=1,SET_KEY='musicBoard.songmap',LS_TAKES='musicBoard.songmap.takes',PPQ=480,MAXREC=15*60e3;
const SIGS=['2/4','3/4','4/4','5/4','6/8','7/8','12/8'];
const mod=(n,m)=>((n%m)+m)%m,clamp=(v,a,b)=>Math.max(a,Math.min(b,v)),now=()=>performance.now();
const esc=s=>String(s??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const SM={},el={};let H=null;

/* =====================================================================================================
   1. Pure logic (no DOM): bars, tempo estimate, chords, form, MIDI file
   A take: {id,name,created,bpm,sig:[num,den],t0,grid:'metro'|'free',key,notes:[{t,m,d,s,v}],ped:[[t,0|1]]}
   Times are ms from the start of the take. bpm counts the signature's own beat (the ♪ in 6/8).
   t0 = where bar one starts. d = how long the key was held, s = how long it sounded (pedal included).
   ===================================================================================================== */
const gridOf=tk=>{const num=tk.sig[0],beat=60000/tk.bpm;return{num,den:tk.sig[1],beat,bar:num*beat,t0:tk.t0,eps:beat/8};};
// first and last bar that hold a note (0 = bar one; −1 = a pickup bar). A note a hair before a bar line belongs to the next bar.
function spanOf(tk){const g=gridOf(tk);if(!tk.notes.length)return{first:0,last:0};let lo=Infinity,hi=-Infinity;
  for(const n of tk.notes){if(n.t<lo)lo=n.t;if(n.t>hi)hi=n.t;}
  return{first:Math.floor((lo-g.t0+g.eps)/g.bar),last:Math.floor((hi-g.t0+g.eps)/g.bar)};}
// bar one for a given bar line c: the bar that holds the first note, or the next one when that note is a pickup (second half of its bar)
function barOne(c,bar,first,eps){const k=Math.floor((first-c+eps)/bar),t0=c+k*bar;return first-t0>bar/2-eps?t0+bar:t0;}

// ---- free playing: estimate the tempo and bar one from the note onsets ----
function estimate(notes,num,Hh){
  const ns=[...notes].sort((a,b)=>a.t-b.t),on=[];
  for(const n of ns){const l=on[on.length-1];   // notes struck together count as one onset
    if(l&&n.t-l.t<35){l.w+=n.v/127;l.lo=Math.min(l.lo,n.m);l.d=Math.max(l.d,n.s||n.d);}else on.push({t:n.t,w:n.v/127,lo:n.m,d:n.s||n.d});}
  if(on.length<4)return null;
  const t1=on[0].t,total=on[on.length-1].t-t1;if(total<1500)return null;
  // how well a grid of period T fits: the onsets as phases on a circle (1 = all aligned). Beat, half beat and quarter beat all count.
  const fit=(T,set)=>{let re=0,im=0,W=0;const k=2*Math.PI/T;for(const o of set){re+=o.w*Math.cos(k*o.t);im+=o.w*Math.sin(k*o.t);W+=o.w;}return Math.hypot(re,im)/W;};
  const score=(bpm,set)=>{const T=60000/bpm;return 0.5*fit(T,set)+0.3*fit(T/2,set)+0.2*fit(T/4,set);};
  // coarse pick on the first 30 s, favouring moderate tempi (the same playing also fits half and double time)
  let D=Math.min(total,30000),sub=on.filter(o=>o.t<=t1+D),best=null;
  for(let bpm=50;bpm<=200;bpm+=0.25){const sc=score(bpm,sub)*Math.exp(-0.5*(Math.log2(bpm/96)/0.55)**2);if(!best||sc>best.sc)best={sc,bpm};}
  // then sharpen it on a longer and longer stretch (a longer stretch pins the tempo more finely)
  let bpm=best.bpm;
  for(;;){const sec=D/1000,r=30/sec,st=1.5/sec;sub=on.filter(o=>o.t<=t1+D);let b2=null;
    for(let b=bpm-r;b<=bpm+r;b+=st){const sc=score(b,sub);if(!b2||sc>b2.sc)b2={sc,bpm:b};}bpm=b2.bpm;if(D>=total)break;D=Math.min(total,D*2);}
  // least squares on the sixteenth-note grid: onset time = phase + k × step
  let T=60000/bpm,st=T/4,ph;{let re=0,im=0;const k=2*Math.PI/st;for(const o of on){re+=o.w*Math.cos(k*o.t);im+=o.w*Math.sin(k*o.t);}ph=mod(Math.atan2(im,re)/(2*Math.PI)*st,st);}
  for(let it=0;it<4;it++){let sw=0,sk=0,sT=0,skk=0,skt=0;
    for(const o of on){const k=Math.round((o.t-ph)/st),r=o.t-ph-k*st;if(Math.abs(r)>st*0.35)continue;sw+=o.w;sk+=o.w*k;sT+=o.w*o.t;skk+=o.w*k*k;skt+=o.w*k*o.t;}
    const den=sw*skk-sk*sk;if(!sw||Math.abs(den)<1e-9)break;const b=(sw*skt-sk*sT)/den;if(!(b>20))break;st=b;ph=(sT-b*sk)/sw;}
  T=st*4;
  // which sixteenth is the beat, then which beat is beat one: where the heavy, long and low onsets fall
  const los=on.map(o=>o.lo).sort((a,b)=>a-b),loCut=los[Math.floor(los.length*0.3)],bar=T*num;
  const str=o=>o.w*(1+Math.min(1,o.d/bar))+(o.lo<=loCut?0.5:0);
  const s4=[0,0,0,0];for(const o of on)s4[mod(Math.round((o.t-ph)/st),4)]+=str(o);
  ph+=s4.indexOf(Math.max(...s4))*st;
  const sd=new Array(num).fill(0),bOf=o=>Math.round((o.t-ph)/T);let sum=0;
  for(const o of on){const b=bOf(o);if(Math.abs(o.t-ph-b*T)<st*0.4){const v=str(o);sd[mod(b,num)]+=v;sum+=v;}}
  sd[mod(bOf(on[0]),num)]+=0.12*sum;   // all else equal, the first note is beat one
  // and the harmony: bars that start on the right beat hold one clean chord each (a bass note and its chord land in the same bar)
  const hs=new Array(num).fill(0),first=on[0].t,last=on[on.length-1].t;
  if(Hh)for(let j=0;j<num;j++){let n=0;for(let a=barOne(ph+j*T,bar,first,T/8);a<last;a+=bar,n++){const d=chordIn(ns,a,a+bar,Hh);
      if(d){const k=(Hh.CHORDS[d.q]||[]).length;hs[j]+=k<=3?1:k===4?0.7:0.3;}}if(n)hs[j]/=n;}
  const mA=Math.max(...sd)||1,mH=Math.max(...hs);let bj=0,bs=-1;
  for(let j=0;j<num;j++){const s=sd[j]/mA+(mH?1.5*hs[j]/mH:0);if(s>bs){bs=s;bj=j;}}
  return{bpm:Math.round(6000000/T)/100,t0:Math.round(barOne(ph+bj*T,bar,first,T/8))};
}

// ---- chords: one chord per bar or half bar (per beat as a last resort), from the notes that sound longest there ----
// A held key counts in full, the pedal's tail for a third, and notes below middle C count more: the left hand names the harmony.
function chordIn(ns,a,b,Hh){const w=new Map(),low=new Map(),ovl=(x,y)=>Math.max(0,Math.min(y,b)-Math.max(x,a));
  for(const n of ns){const k=n.t+Math.max(n.d,60),e=Math.max(k,n.t+n.s);if(n.t>=b||e<=a)continue;if(ovl(n.t,e)<Math.min(50,(b-a)*0.1))continue;
    const pc=mod(n.m,12),x=(ovl(n.t,k)+0.35*ovl(k,e))*(0.4+0.6*n.v/127)*(n.m<60?1:0.6);
    w.set(pc,(w.get(pc)||0)+x);if(!low.has(pc)||n.m<low.get(pc))low.set(pc,n.m);}
  if(w.size<2)return null;const mx=Math.max(...w.values()),pcs=[...w].filter(x=>x[1]>=0.3*mx).sort((p,q)=>q[1]-p[1]);   // short passing notes don't count
  while(pcs.length>=2){const d=Hh.detectChord(pcs.map(x=>low.get(x[0])));if(d)return d;if(pcs.length<=3)break;pcs.pop();}return null;}
const sameChord=(a,b)=>!!a&&!!b&&a.r===b.r&&a.q===b.q;
function chordTrack(tk,g,sp,Hh){const ns=tk.notes,raw=[],halves=g.num%2===0;
  const beats=(a,i0,i1)=>{for(let i=i0;i<i1;i++){const d=chordIn(ns,a+i*g.beat,a+(i+1)*g.beat,Hh);if(d)raw.push({a:a+i*g.beat,b:a+(i+1)*g.beat,d});}};
  for(let b=sp.first;b<=sp.last;b++){const a=g.t0+b*g.bar,m=a+g.bar/2,z=a+g.bar,whole=chordIn(ns,a,z,Hh);
    if(halves){const h1=chordIn(ns,a,m,Hh),h2=chordIn(ns,m,z,Hh);
      if(h1&&h2){if(sameChord(h1,h2))raw.push({a,b:z,d:h1});else raw.push({a,b:m,d:h1},{a:m,b:z,d:h2});}
      else if(whole)raw.push({a,b:z,d:whole});
      else{if(h1)raw.push({a,b:m,d:h1});else beats(a,0,g.num/2);if(h2)raw.push({a:m,b:z,d:h2});else beats(a,g.num/2,g.num);}
    }else if(whole)raw.push({a,b:z,d:whole});else beats(a,0,g.num);}
  const segs=[];
  for(const s of raw){const l=segs[segs.length-1];if(l&&sameChord(l.d,s.d)&&Math.abs(l.b-s.a)<1){l.b=s.b;continue;}segs.push({...s});}
  const key=Hh.key();
  for(const s of segs){const root=Hh.spellPc(s.d.r),bass=s.d.bass!==s.d.r?Hh.spellPc(s.d.bass):null;
    s.sym=root.name+(Hh.SYM[s.d.q]??'')+(bass?'/'+bass.name:'');s.roman=Hh.romanFor(root,s.d.q,key)||'';
    s.bar0=Math.round((s.a-g.t0)/g.bar*2)/2;s.bar1=Math.round((s.b-g.t0)/g.bar*2)/2;}
  return segs;}
// the role of a note inside a chord, as the board colours it (root, third, fifth, seventh, tension); null = not a chord note
function roleIn(d,m,Hh){const iv=mod(m-d.r,12);
  for(const tok of Hh.CHORDS[d.q]||[]){const p=Hh.parseDeg(tok);if(mod(p.semis,12)!==iv)continue;
    return p.d===1?'root':p.d===3?'third':p.d===5?'fifth':p.d===7||(p.d===6&&/6/.test(d.q))?'seventh':'tension';}return null;}

// ---- form: compare the four-bar phrases (same notes on the same sixteenths, same chords on the same beats) and letter them ----
function formOf(tk,g,sp,segs){const st=g.beat/4,per=16*g.num,nP=Math.max(1,Math.ceil((sp.last+1)/4)),ph=[];
  for(let p=0;p<nP;p++)ph.push({p,bar0:p*4,bar1:Math.min(p*4+3,Math.max(sp.last,0)),S:new Set(),C:[],label:''});
  for(const n of tk.notes){const k=Math.round((n.t-g.t0)/st);if(k<0)continue;const p=Math.floor(k/per);if(ph[p])ph[p].S.add((k%per)+':'+n.m);}
  let si=0;for(const P of ph)for(let i=0;i<4*g.num;i++){const t=g.t0+(P.p*4*g.num+i+0.5)*g.beat;while(si<segs.length&&segs[si].b<=t)si++;
    const s=segs[si];P.C.push(s&&s.a<=t?s.d.r+':'+s.d.q:'');}
  const sim=(A,B)=>{let inter=0;for(const x of A.S)if(B.S.has(x))inter++;const uni=A.S.size+B.S.size-inter,J=uni?inter/uni:1;
    let tot=0,eq=0;for(let i=0;i<A.C.length;i++){if(!A.C[i]&&!B.C[i])continue;tot++;if(A.C[i]===B.C[i])eq++;}return tot?0.6*J+0.4*eq/tot:J;};
  const reps=[];let letters=0;   // reps: one phrase for every label given so far
  for(const P of ph){if(!P.S.size){P.label='–';continue;}let best=null;
    for(const r of reps){const s=sim(P,r.P);if(!best||s>best.s)best={s,r};}
    if(best&&best.s>=0.8){P.label=best.r.P.label;P.like=best.r.P.p;P.sim=best.s;continue;}
    if(best&&best.s>=0.45){const L=best.r.letter,n=reps.filter(r=>r.letter===L).length;P.label=L+'′'.repeat(Math.min(n,3));P.like=best.r.P.p;P.sim=best.s;reps.push({letter:L,P});continue;}
    const L=String.fromCharCode(65+(letters++%26));P.label=L;reps.push({letter:L,P});}
  return ph;}

function analyse(tk,Hh){const g=gridOf(tk),sp=spanOf(tk),segs=chordTrack(tk,g,sp,Hh),form=formOf(tk,g,sp,segs);
  const roles=[];let si=0;const order=tk.notes.map((n,i)=>i).sort((a,b)=>tk.notes[a].t-tk.notes[b].t);
  for(const i of order){const n=tk.notes[i],t=n.t+g.eps;while(si<segs.length&&segs[si].b<=t)si++;const s=segs[si];roles[i]=s&&s.a<=t?roleIn(s.d,n.m,Hh):null;}
  return{g,sp,segs,form,roles,rows:[...new Set(tk.notes.map(n=>n.m))].sort((a,b)=>b-a)};}

// ---- Standard MIDI File (format 1: a tempo track + one note track named after the recording) ----
const vlq=n=>{const b=[n&127];while((n>>=7)>0)b.unshift((n&127)|128);return b;};
const u32=n=>[(n>>>24)&255,(n>>>16)&255,(n>>>8)&255,n&255],u16=n=>[(n>>8)&255,n&255];
const utf8=s=>[...new TextEncoder().encode(s)];
function keySf(key,Hh){if(!key)return{sf:0,mi:0};const off=Hh.MODE_OFFSET[key.mode]||0,idx=[0,7,2,9,4,11,6,1,8,3,10,5].indexOf(mod(key.tonic.pc-off,12));
  return{sf:idx<=6?idx:idx-12,mi:off===9?1:0};}
// o: {name, a, b (the stretch of the take, in ms; whole bars), sf, mi, pedal}
function buildMidi(tk,o){const g=gridOf(tk),tpb=PPQ*4/g.den,tick=t=>Math.round((t-o.a)/g.beat*tpb),end=Math.max(tpb,tick(o.b)),ev=[];let count=0;
  for(const n of tk.notes){if(n.t<o.a-g.eps||n.t>=o.b-g.eps)continue;const t1=clamp(tick(n.t),0,end-1),t2=clamp(tick(n.t+n.d),t1+1,end);
    ev.push([t1,2,0x90,n.m,clamp(Math.round(n.v),1,127)],[t2,0,0x80,n.m,0]);count++;}
  if(o.pedal){let down=false,started=false;const start=()=>{if(!started){started=true;if(down)ev.push([0,1,0xB0,64,127]);}};
    for(const[t,on]of tk.ped){if(t<o.a){down=!!on;continue;}if(t>=o.b)break;start();down=!!on;ev.push([clamp(tick(t),0,end),1,0xB0,64,on?127:0]);}
    start();if(down)ev.push([end,0,0xB0,64,0]);}
  ev.sort((x,y)=>x[0]-y[0]||x[1]-y[1]);
  const meta=(type,data)=>[0xFF,type,...vlq(data.length),...data],name=utf8(o.name||'Take');
  const trk=body=>[0x4D,0x54,0x72,0x6B,...u32(body.length),...body];
  const us=Math.round(60e6/(tk.bpm*4/g.den));
  const t0=[0,...meta(3,name),0,...meta(0x51,[(us>>16)&255,(us>>8)&255,us&255]),0,...meta(0x58,[g.num,Math.log2(g.den),96/g.den,8]),
    0,...meta(0x59,[o.sf&255,o.mi?1:0]),...vlq(end),...meta(0x2F,[])];
  const t1=[0,...meta(3,name)];let last=0;for(const e of ev){t1.push(...vlq(e[0]-last),e[2],e[3],e[4]);last=e[0];}
  t1.push(...vlq(end-last),...meta(0x2F,[]));
  return{bytes:new Uint8Array([0x4D,0x54,0x68,0x64,...u32(6),...u16(1),...u16(2),...u16(PPQ),...trk(t0),...trk(t1)]),count,endTick:end};}
// reads a MIDI file back (used to check every export before it is saved)
function parseMidi(u8){let p=0;const rd=n=>{let v=0;while(n--)v=v*256+u8[p++];return v;},str=n=>{const s=new TextDecoder().decode(u8.subarray(p,p+n));p+=n;return s;},
    rv=()=>{let v=0,b;do{b=u8[p++];v=(v<<7)|(b&127);}while(b&128);return v;};
  if(str(4)!=='MThd')throw new Error('not a MIDI file');const hl=rd(4),format=rd(2),ntrks=rd(2),ppq=rd(2);p+=hl-6;
  const out={format,ntrks,ppq,tempo:null,sig:null,key:null,tracks:[]};
  for(let k=0;k<ntrks;k++){if(str(4)!=='MTrk')throw new Error('bad track');const len=rd(4),endP=p+len,tr={name:'',notes:[],cc:[],end:0};let tick=0,run=0;const open=new Map();
    while(p<endP){tick+=rv();let st=u8[p];if(st&128)p++;else st=run;
      if(st===0xFF){const type=u8[p++],l=rv();
        if(type===3)tr.name=str(l);else{const d=u8.subarray(p,p+l);p+=l;
          if(type===0x51)out.tempo=(d[0]<<16)|(d[1]<<8)|d[2];else if(type===0x58)out.sig=[d[0],2**d[1]];
          else if(type===0x59)out.key={sf:d[0]>127?d[0]-256:d[0],mi:d[1]};else if(type===0x2F)tr.end=tick;}}
      else if(st===0xF0||st===0xF7){p+=rv();}
      else{run=st;const c=st&0xF0,d1=u8[p++],d2=c===0xC0||c===0xD0?0:u8[p++];
        if(c===0x90&&d2>0)open.set(d1,{tick,m:d1,v:d2,dur:0});
        else if(c===0x80||c===0x90){const n=open.get(d1);if(n){n.dur=tick-n.tick;tr.notes.push(n);open.delete(d1);}}
        else if(c===0xB0)tr.cc.push({tick,cc:d1,v:d2});}}
    p=endP;tr.hung=open.size;tr.notes.sort((a,b)=>a.tick-b.tick);out.tracks.push(tr);}
  return out;}

/* =====================================================================================================
   2. Settings and the library (kept in this browser)
   ===================================================================================================== */
const DEF={detail:'notes',view:'fit',loop:false,names:true,pedalX:true,bpm:96,sig:'4/4',ci:1,tick:'tick',vol:'medium',cur:''};
const OK={detail:['notes','chords','form'],view:['fit','8','16'],sig:SIGS,ci:[0,1,2],tick:['tick','fifth'],vol:['soft','medium','loud']};
const S={...DEF};
function setLoad(){try{const s=JSON.parse(localStorage.getItem(SET_KEY));if(s&&s.v===VERSION)for(const k in DEF)if(typeof s[k]===typeof DEF[k]&&(!OK[k]||OK[k].includes(s[k])))S[k]=s[k];}catch(e){}
  S.bpm=clamp(Math.round(S.bpm)||96,30,300);}
function setSave(){try{localStorage.setItem(SET_KEY,JSON.stringify({v:VERSION,...S}));}catch(e){}}
const sigArr=()=>S.sig.split('/').map(Number);

let takes=[],cur=null,sel=null,an=null,anKey='';   // sel = [first bar, last bar] (0 = bar one), or null
const r1=x=>Math.round(x);
const pack=tk=>({v:VERSION,id:tk.id,name:tk.name,created:tk.created,bpm:tk.bpm,sig:tk.sig,t0:tk.t0,grid:tk.grid,key:tk.key,
  n:tk.notes.map(n=>[r1(n.t),n.m,r1(n.d),n.v,r1(n.s)]),p:tk.ped});
const unpack=r=>({id:r.id,name:r.name,created:r.created,bpm:r.bpm,sig:r.sig,t0:r.t0,grid:r.grid,key:r.key||'',
  notes:(r.n||[]).map(a=>({t:a[0],m:a[1],d:a[2],v:a[3],s:a[4]})),ped:r.p||[]});
const validTake=r=>r&&typeof r.id==='string'&&r.bpm>0&&Array.isArray(r.sig)&&Array.isArray(r.n);
const DB={db:null,
  open(){return new Promise(res=>{try{const r=indexedDB.open('tonos-songmap',1);r.onupgradeneeded=()=>r.result.createObjectStore('takes',{keyPath:'id'});
    r.onsuccess=()=>{DB.db=r.result;res(true);};r.onerror=r.onblocked=()=>res(false);}catch(e){res(false);}});},
  tx(mode,fn){return new Promise(res=>{try{const t=DB.db.transaction('takes',mode),q=fn(t.objectStore('takes'));t.oncomplete=()=>res(q?q.result:true);t.onerror=t.onabort=()=>res(null);}catch(e){res(null);}});},
  lsAll(){try{const s=JSON.parse(localStorage.getItem(LS_TAKES));return s&&s.v===VERSION&&Array.isArray(s.takes)?s.takes:[];}catch(e){return[];}},
  lsSave(){try{localStorage.setItem(LS_TAKES,JSON.stringify({v:VERSION,takes:takes.map(pack)}));}catch(e){}},
  async all(){if(DB.db){const r=await DB.tx('readonly',s=>s.getAll());if(r)return r;}return DB.lsAll();},
  put(tk){if(DB.db)return DB.tx('readwrite',s=>s.put(pack(tk)));DB.lsSave();},
  del(id){if(DB.db)return DB.tx('readwrite',s=>s.delete(id));DB.lsSave();}};
function analysis(){if(!cur)return null;const k=[cur.id,cur.bpm,cur.t0,cur.sig,cur.notes.length,H.key()?.label,H.scale()?.label].join('|');
  if(k!==anKey||!an){an=analyse(cur,H);anKey=k;}return an;}
function select(tk){cur=tk||null;sel=null;an=null;S.cur=cur?cur.id:'';T.flash='';setSave();if(T.mode==='play')playStop();layoutView();ui();renderLib();draw();}
function saveTake(tk){an=null;return DB.put(tk);}

/* =====================================================================================================
   3. Transport: metronome, recording, playback (one clock: performance.now(); sound is scheduled a little ahead)
   ===================================================================================================== */
const T={mode:'idle',metro:false,origin:0,lat:0,live:null,P:null,M:{next:0,i:0},timer:0,raf:0,pick:false,pedal:false,flash:'',flashT:0,taps:[]};
const isLive=()=>T.mode==='armed'||T.mode==='countin'||T.mode==='rec';
const audioAt=tp=>{const c=H.ac();return Math.max(c.currentTime,c.currentTime+(tp-now())/1000);};
const latency=()=>{try{const c=H.ac();return clamp(((c.outputLatency||0)+(c.baseLatency||0))*1000,0,300);}catch(e){return 0;}};
const tonicMidi=()=>{const k=H.scale()||H.key(),pc=k?k.tonic.pc:0;return 72+pc-(pc>6?12:0);};   // G4 … F♯5
// beat one sounds the tonic of the selected scale; the other beats a soft tick, or the fifth
function click(tp,i){try{const at=audioAt(tp),vol={soft:0.5,medium:1,loud:1.8}[S.vol],ton=tonicMidi();
    if(i===0)H.tone(ton,at,0.22,0.2*vol);else if(S.tick==='fifth')H.tone(ton+7,at,0.14,0.07*vol);
    else{const c=H.ac(),o=c.createOscillator(),g=c.createGain();o.type='sine';o.frequency.value=1400;g.gain.setValueAtTime(0.06*vol,at);g.gain.exponentialRampToValueAtTime(0.0001,at+0.05);
      o.connect(g).connect(H.master());o.start(at);o.stop(at+0.06);}}catch(e){}
  setTimeout(()=>dotFlash(i),Math.max(0,tp-now()));}
function engineOn(){if(!T.timer)T.timer=setInterval(engine,25);}
function engineOff(){if(T.timer&&T.mode==='idle'&&!T.metro){clearInterval(T.timer);T.timer=0;dotFlash(-1);}}
function engine(){const t=now(),LA=120;
  if(T.mode==='countin'&&t>=T.origin){T.mode='rec';ui();}
  if(T.mode==='rec'&&t-T.origin>MAXREC){recStop();return;}
  if(T.mode==='play'){playSched(t,LA);return;}
  if(isLive())status();   // the count keeps going even when the page can't draw frames
  if(T.metro){const M=T.M,num=(isLive()?T.live.sig:sigArr())[0],beat=60000/(isLive()?T.live.bpm:S.bpm);
    if(M.next<t-250){M.next=t+60;M.i=0;}   // the tab was asleep: start again on beat one instead of catching up
    while(M.next<t+LA){click(M.next,M.i);M.i=(M.i+1)%num;M.next+=beat;}}}
function loopOn(){if(!T.raf){const f=()=>{T.raf=0;if(T.mode==='idle')return;status();draw();T.raf=requestAnimationFrame(f);};T.raf=requestAnimationFrame(f);}}
function metroSet(on){T.metro=on;if(on){try{H.ac();}catch(e){}T.M.next=now()+80;T.M.i=0;engineOn();}else engineOff();ui();}

// ---- recorder (times already relative to the take) ----
function recOn(L,t,m,v){const i=L.sus.findIndex(n=>n.m===m);if(i>=0){const n=L.sus[i];n.s=Math.max(n.d,t-n.t);n.open=false;L.sus.splice(i,1);}   // struck again while the pedal held it
  const p=L.down.get(m);if(p){p.d=p.s=Math.max(1,t-p.t);p.open=false;}
  const n={t,m,v:clamp(Math.round(v)||100,1,127),d:0,s:0,open:true};L.notes.push(n);L.down.set(m,n);}
function recOff(L,t,m){const n=L.down.get(m);if(!n)return;L.down.delete(m);n.d=Math.max(1,t-n.t);if(L.pedal)L.sus.push(n);else{n.s=n.d;n.open=false;}}
function recPedal(L,t,on){on=!!on;if(on===L.pedal)return;L.pedal=on;L.ped.push([Math.round(t),on?1:0]);
  if(!on){for(const n of L.sus){n.s=Math.max(n.d,t-n.t);n.open=false;}L.sus=[];}}
function recClose(L,t){for(const n of L.down.values()){n.d=Math.max(1,t-n.t);n.s=n.d;n.open=false;}L.down.clear();
  for(const n of L.sus){n.s=Math.max(n.d,t-n.t);n.open=false;}L.sus=[];if(L.pedal){L.pedal=false;L.ped.push([Math.round(t),0]);}}
const newLive=(grid,bpm,sig)=>({grid,bpm,sig,notes:[],ped:[],down:new Map(),sus:[],pedal:false});
const relT=tp=>Math.max(0,tp-T.origin-(T.live.grid==='metro'?T.lat:0));
function nextName(){let n=0;for(const t of takes){const m=/^Take (\d+)$/.exec(t.name);if(m)n=Math.max(n,+m[1]);}return'Take '+(n+1);}
function finish(L,name,dry){const notes=L.notes.map(n=>({t:n.t,m:n.m,d:n.d,s:Math.max(n.s,n.d),v:n.v})).sort((a,b)=>a.t-b.t||a.m-b.m);if(!notes.length)return null;
  const tk={id:'t'+Date.now().toString(36)+Math.floor(Math.random()*1296).toString(36),name:name||nextName(),created:Date.now(),bpm:L.bpm,sig:L.sig,t0:0,grid:L.grid,
    key:H.key()?.label||'',notes,ped:L.ped};
  if(L.grid==='free'){const e=estimate(notes,L.sig[0],H);if(e){tk.bpm=e.bpm;tk.t0=e.t0;}}   // too few notes to guess: the metronome's tempo, bar one at the first note
  if(!dry){takes.unshift(tk);saveTake(tk);}return tk;}
function recStart(){if(T.mode==='play')playStop();if(T.mode!=='idle')return;pickSet(false);const sig=sigArr();
  T.live=newLive(T.metro?'metro':'free',S.bpm,sig);
  if(T.metro){try{H.ac();}catch(e){}T.lat=latency();const beat=60000/S.bpm;T.M.next=now()+120;T.M.i=0;T.origin=T.M.next+S.ci*sig[0]*beat;T.mode=S.ci?'countin':'rec';}
  else{T.lat=0;T.origin=0;T.mode='armed';}
  if(T.pedal&&T.mode!=='armed'){T.live.pedal=true;T.live.ped.push([0,1]);}
  el.scroll.scrollLeft=0;engineOn();loopOn();layoutView();ui();draw();}
function recStop(){if(!isLive())return;const L=T.live,armed=T.mode!=='rec'&&!L.notes.length,tEnd=armed?0:relT(now());T.mode='idle';T.live=null;
  if(!armed)recClose(L,tEnd);const tk=armed?null:finish(L);
  if(T.metro){T.M.next=now()+60000/S.bpm;T.M.i=0;}engineOff();
  if(tk){select(tk);flash(tk.grid==='free'?`Saved · tempo guessed at ${tk.bpm.toFixed(1)} bpm`:'Saved');}else{flash('Nothing recorded');layoutView();ui();draw();}}

// ---- playback through the board's sound; with a selection it plays those bars, and loops them when Loop is on ----
function playRange(){const a=analysis(),g=a.g,b0=sel?sel[0]:a.sp.first,b1=sel?sel[1]:a.sp.last;return{a:g.t0+b0*g.bar,b:g.t0+(b1+1)*g.bar};}
function playStart(){if(!cur||isLive())return;if(T.mode==='play')playStop();pickSet(false);const a=analysis(),g=a.g,R=playRange(),ev=[];
  for(const n of cur.notes)if(n.t>=R.a-g.eps&&n.t<R.b-g.eps)ev.push({t:Math.max(0,n.t-R.a),m:n.m,dur:clamp(Math.max(n.s,n.d)/1000+0.25,0.3,8),g:0.04+0.2*n.v/127});
  const cl=[];for(let j=Math.ceil((R.a-g.t0)/g.beat-1e-6);g.t0+j*g.beat<R.b-1;j++)cl.push({t:g.t0+j*g.beat-R.a,i:mod(j,g.num)});
  try{H.ac();}catch(e){}T.P={a:R.a,len:R.b-R.a,origin:now()+90,sv:0,loop:S.loop,ev,cl};T.mode='play';engineOn();loopOn();ui();}
function playSched(t,LA){const P=T.P,vEnd=t-P.origin+LA;
  while(P.sv<vEnd){const k=Math.floor(P.sv/P.len+1e-9);if(k>0&&!P.loop)break;const base=k*P.len,x0=P.sv-base,x1=Math.min(vEnd-base,P.len);
    for(const e of P.ev)if(e.t>=x0&&e.t<x1){try{H.tone(e.m,audioAt(P.origin+base+e.t),e.dur,e.g);}catch(_){}}
    if(T.metro)for(const c of P.cl)if(c.t>=x0&&c.t<x1)click(P.origin+base+c.t,c.i);
    P.sv=base+x1;if(x1<P.len)break;}
  if(!P.loop&&t-P.origin>=P.len+150)playStop();}
function playPos(){const P=T.P;if(!P)return null;const v=now()-P.origin;if(v<0)return P.a;return P.a+(P.loop?v%P.len:Math.min(v,P.len));}
function playStop(){if(T.mode!=='play')return;T.mode='idle';T.P=null;if(T.metro){T.M.next=now()+60000/S.bpm;T.M.i=0;}engineOff();ui();draw();}

/* =====================================================================================================
   4. The block: markup, styles, drawing, controls
   ===================================================================================================== */
const CSS=`
.sm{display:flex;flex-direction:column;gap:12px;min-width:0}
.sm-row{display:flex;gap:8px 12px;justify-content:center;align-items:center;flex-wrap:wrap}
.sm button:disabled,.sm input:disabled,.sm select:disabled{opacity:.35;cursor:default}
.sm-main{min-width:84px}
#smRec.on{border-color:var(--live);color:var(--live)}
.sm-st{height:22px;text-align:center;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font:11px/22px var(--mono);letter-spacing:.06em;text-transform:uppercase;color:var(--muted)}
.sm-st b{font:600 14px/22px var(--body);letter-spacing:0;text-transform:none;color:var(--ink);margin-right:10px}
.sm-st.rec{color:var(--live)}
.sm-fig{margin:0;min-width:0}
.sm-scroll{overflow-x:auto;overflow-y:hidden;scrollbar-width:thin;border:1px solid var(--line);border-radius:8px}
.sm-spacer{height:0}
.sm-scroll canvas{display:block;position:sticky;left:0;width:100%;height:240px;touch-action:pan-x pan-y;cursor:crosshair}
.sm-scroll canvas.pick{cursor:cell}
.sm-cap{font:10.5px var(--mono);letter-spacing:.06em;text-transform:uppercase;color:var(--muted);text-align:center;margin-top:8px;height:16px;line-height:16px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.sm-num,.sm-sel{font:500 12.5px var(--mono);min-height:28px;padding:3px 10px;border-radius:999px;border:1px solid var(--line);background:var(--bg);color:var(--ink)}
.sm-num{width:8ch;text-align:center}
.sm-sel{cursor:pointer}
.sm-val{display:inline-block;min-width:6ch;text-align:center;font:500 12.5px var(--mono);letter-spacing:0;color:var(--ink)}
.sm-dots{display:inline-flex;gap:5px;align-items:center;height:28px;min-width:118px;justify-content:center}
.sm-dots i{width:8px;height:8px;border-radius:50%;border:1px solid var(--muted);display:inline-block}
.sm-dots i.on{background:var(--ink);border-color:var(--ink)}
.sm-dots i.on:first-child{background:var(--accent);border-color:var(--accent)}
.sm-sep{width:1px;height:18px;background:var(--line)}
.sm-lib{display:flex;gap:6px;flex-wrap:nowrap;height:36px;align-items:center;overflow-x:auto;overflow-y:hidden;scrollbar-width:thin}
.sm-lib>:first-child{margin-left:auto}.sm-lib>:last-child{margin-right:auto}
.sm-lib .none{font:10.5px var(--mono);letter-spacing:.06em;text-transform:uppercase;color:var(--muted);opacity:.7;white-space:nowrap}
.sm-tk{flex:none;display:inline-flex;align-items:center;height:30px;border:1px solid var(--line);border-radius:999px;white-space:nowrap}
.sm-tk.on{border-color:var(--ink)}
.sm-tk button{border:0;min-height:28px;padding:3px 10px;font-size:12.5px;color:var(--muted)}
.sm-tk button:hover{color:var(--ink)}
.sm-tk.on .sm-tk-n{color:var(--ink);font-weight:600}
.sm-tk small{font:10.5px var(--mono);letter-spacing:.04em;color:var(--muted);margin-left:8px;font-weight:400}
.sm-tk .sm-tk-i{padding:3px 8px}
.sm-tk .ask{font:10.5px var(--mono);letter-spacing:.06em;text-transform:uppercase;color:var(--live);padding:0 4px 0 12px}
.sm-tk input{font:inherit;font-size:12.5px;width:18ch;margin:0 4px 0 10px;padding:2px 6px;border:0;border-bottom:1px solid var(--muted);background:none;color:var(--ink);outline:none}
.board>.sized>.sm{flex:1 1 0;min-height:320px}
.board>.sized .sm-fig{flex:1 1 0;display:flex;flex-direction:column;min-height:120px}
.board>.sized .sm-scroll{flex:1 1 0;display:flex;flex-direction:column;min-height:100px}
.board>.sized .sm-scroll canvas{flex:1 1 0;height:auto;min-height:100px}
`;
const h=(title,text)=>`data-help-title="${esc(title)}" data-help="${esc(text)}"`;
const TPL=`
<h2 ${h('Song map','Records what you play and draws it as a map of the song: bars across, one row for each note you used. The same take can be read as notes, as chords or as phrases.')}>Song map</h2>
<button class="opt-btn" id="smOptBtn" data-pop="smOpts" aria-label="Song map options" aria-haspopup="true" aria-expanded="false" title="Song map options" ${h('Options','The metronome\'s count-in, sound and volume, how many bars the map shows across, and what goes into the MIDI file. Your choices are remembered in this browser.')}>⚙</button>
<div class="opt-pop" id="smOpts" role="group" aria-label="Song map options">
  <div class="opt-h">Metronome</div>
  <span class="tl" ${h('Count-in','How many bars the metronome counts before the recording starts. Off starts recording at once.')}>Count-in<span class="seg" id="smCi" role="group" aria-label="Count-in"><button data-v="0">Off</button><button data-v="1">1 bar</button><button data-v="2">2 bars</button></span></span>
  <span class="tl" ${h('Metronome · other beats','Beat one always sounds the home note of the selected scale. The other beats can be a soft tick, or the fifth of the scale.')}>Other beats<span class="seg" id="smTick" role="group" aria-label="Sound of the other beats"><button data-v="tick">Tick</button><button data-v="fifth">Fifth</button></span></span>
  <span class="tl" ${h('Metronome · volume','How loud the metronome is. It does not change the recording.')}>Volume<span class="seg" id="smVol" role="group" aria-label="Metronome volume"><button data-v="soft">Soft</button><button data-v="medium">Medium</button><button data-v="loud">Loud</button></span></span>
  <div class="opt-h">Map</div>
  <span class="tl" ${h('Map · bars across','How many bars fit across the map. All shows the whole take; 8 or 16 zooms in, and you scroll sideways for the rest.')}>Bars across<span class="seg" id="smView" role="group" aria-label="Bars across"><button data-v="fit">All</button><button data-v="8">8</button><button data-v="16">16</button></span></span>
  <label class="toggle" ${h('Map · note names','Shows the name of each row\'s note at the left edge of the map, spelled in the selected scale.')}><input type="checkbox" id="smNames"> note names</label>
  <div class="opt-h">MIDI file</div>
  <label class="toggle" ${h('MIDI file · pedal','Writes your sustain-pedal moves into the MIDI file, so the clip in Ableton rings like your playing.')}><input type="checkbox" id="smPedalX"> include the pedal</label>
</div>
<div class="sm">
  <div class="sm-row">
    <button class="sm-main" id="smRec" ${h('Record','Starts recording what you play on the MIDI keyboard. With the metronome on, it counts in first and the bars are exact. With it off, recording starts at your first note and the bars are worked out afterwards. Press again to stop and save.')}>● Rec</button>
    <button class="sm-main" id="smPlay" ${h('Play','Plays the recording through the board\'s sound. If you selected bars on the map, it plays only those.')}>▶ Play</button>
    <button class="tool" id="smLoop" aria-pressed="false" ${h('Loop','Repeats the selected bars (or the whole take) until you press Stop. Good for practising over a phrase.')}>Loop</button>
    <span class="sm-sep" aria-hidden="true"></span>
    <span class="tl" ${h('Detail','How closely the map reads the take. Notes: every note, grey inside the scale and pink outside it. Chords: one block per chord with its name and roman numeral, and the notes coloured by their role in the chord. Form: the four-bar phrases compared and lettered, so A A B A′ shows the shape of the song.')}>Detail<span class="seg" id="smDetail" role="group" aria-label="Detail"><button data-v="notes">Notes</button><button data-v="chords">Chords</button><button data-v="form">Form</button></span></span>
  </div>
  <div class="sm-st" id="smSt" role="status" ${h('Recording','The name of the recording on the map, with its length, tempo and time signature. While recording it shows where you are.')}></div>
  <figure class="sm-fig"><div class="sm-scroll" id="smScroll"><div class="sm-spacer" id="smSpacer"></div><canvas id="smMap" aria-label="Song map" ${h('Song map','Time runs left to right. Thin lines are bars, stronger lines every four bars. Each row is one note you played. Drag across bars to select them (for Play, Loop and the MIDI file); click the selection again to clear it.')}></canvas></div>
    <figcaption class="sm-cap" id="smCap"></figcaption></figure>
  <div class="sm-row">
    <button class="tool" id="smMetro" aria-pressed="false" ${h('Metronome','Turns the click on. Beat one sounds the home note of the selected scale. Record with it on and every bar lands exactly on the grid.')}>Metronome</button>
    <span class="tl" ${h('Metronome · tempo','Beats per minute. Type a number or use the arrows. It is locked while recording.')}>Tempo<input class="sm-num" id="smBpm" type="number" min="30" max="300" step="1" inputmode="numeric" aria-label="Tempo in beats per minute"></span>
    <button class="tool" id="smTap" ${h('Tap tempo','Tap this button in time, four or more times, and the tempo follows your taps.')}>Tap</button>
    <select class="sm-sel" id="smSig" aria-label="Time signature" ${h('Time signature','How many beats in a bar, and which note is the beat. It sets the metronome and how new recordings are split into bars.')}>${SIGS.map(s=>`<option>${s}</option>`).join('')}</select>
    <span class="sm-dots" id="smDots" aria-hidden="true" ${h('Beat lights','One light per beat of the bar. The gold one is beat one.')}></span>
  </div>
  <div class="sm-row">
    <span class="tl" ${h('Bars · tempo of this take','Fixes the bar lines of this recording when the guess is a little off. Minus and plus move the tempo by half a beat per minute: watch the lines slide onto your notes. ½ and ×2 fix a guess that is half or double the real tempo. It never changes the notes.')}>Bars<span class="seg" id="smNudge" role="group" aria-label="Tempo of this take"><button data-d="-0.5" aria-label="Slower">−</button><b class="sm-val" id="smTval">—</b><button data-d="0.5" aria-label="Faster">+</button><button data-f="0.5">½</button><button data-f="2">×2</button></span></span>
    <button class="tool" id="smOne" aria-pressed="false" ${h('This is beat one','Press it, then click the note on the map that starts a bar. All the bar lines move so that note is beat one.')}>This is beat one</button>
    <span class="sm-sep" aria-hidden="true"></span>
    <button class="tool" id="smExport" ${h('MIDI file','Downloads the take (or the selected bars) as a MIDI file with its tempo, time signature, key and name. Drag the file into a clip slot in Ableton Live.')}>MIDI file ↓</button>
    <button class="tool" id="smUse" ${h('Use as progression','Sends the chords found in this take (or in the selected bars) to the Progression block, so you can step through them on the keyboard.')}>Use as progression</button>
  </div>
  <div class="sm-lib" id="smLib" ${h('Recordings','Every take you recorded, newest first, kept in this browser. Click one to put it on the map. On the current one: ✎ renames it and × deletes it (it asks first).')}></div>
</div>`;

function cols(){const cs=getComputedStyle(document.documentElement),v=n=>cs.getPropertyValue(n).trim();
  return{line:v('--line'),ink:v('--ink'),muted:v('--muted'),inscale:v('--inscale')||v('--muted'),outscale:v('--outscale')||'#ff6fa3',root:v('--root'),third:v('--third'),
    fifth:v('--fifth'),seventh:v('--seventh'),tension:v('--tension'),accent:v('--accent'),live:v('--live'),mono:v('--mono')||'monospace',display:v('--display')||'sans-serif'};}
function fit(cv){const d=window.devicePixelRatio||1,w=cv.clientWidth,hh=cv.clientHeight,W=Math.max(1,Math.round(w*d)),Hh=Math.max(1,Math.round(hh*d));
  if(cv.width!==W||cv.height!==Hh){cv.width=W;cv.height=Hh;}const g=cv.getContext('2d');g.setTransform(d,0,0,d,0,0);return[g,w,hh];}
function rr(g,x,y,w,hh,r){g.beginPath();if(g.roundRect)g.roundRect(x,y,w,hh,r);else g.rect(x,y,w,hh);}
const GUT=()=>S.names?36:8,PR=8,RUL=16,FORM_H=28,CH_H=40;
// what the map shows: live → from the start, growing in steps (8, 16, 32 bars…); a take → all of it, or a window you scroll
function viewOf(){if(isLive()){const L=T.live,t=T.mode==='rec'?Math.max(0,now()-T.origin):0;
    if(L.grid==='metro'){const bar=L.sig[0]*60000/L.bpm;let n=8;while(t>=n*bar)n*=2;return{a:0,b:n*bar,A:0,B:n*bar};}
    let s=20000;while(t>=s)s*=2;return{a:0,b:s,A:0,B:s};}
  const a=analysis(),g=a.g,A=g.t0+a.sp.first*g.bar,B=g.t0+(a.sp.last+1)*g.bar,nb=a.sp.last-a.sp.first+1,N=S.view==='fit'?nb:Math.min(nb,+S.view),frac=N/nb;
  const sc=el.scroll,max=sc.scrollWidth-sc.clientWidth,pos=max>0?sc.scrollLeft/max:0,va=A+(B-A)*(1-frac)*pos;return{a:va,b:va+(B-A)*frac,A,B};}
function layoutView(){let w=100;if(!isLive()&&cur){const a=analysis(),nb=a.sp.last-a.sp.first+1;if(S.view!=='fit'&&nb>+S.view)w=100*nb/+S.view;}
  el.spacer.style.width=w+'%';if(w===100)el.scroll.scrollLeft=0;}
// keep the playhead on screen: when it leaves the window, turn the page
function follow(pos,V){if(pos>=V.a&&pos<V.b)return;const sc=el.scroll,max=sc.scrollWidth-sc.clientWidth;if(max<=0)return;const w=V.b-V.a,page=Math.floor((pos-V.A)/w);
  sc.scrollLeft=clamp(page*w/((V.B-V.A)-w),0,1)*max;}
function inScaleSet(){const s=H.scale()||H.key();return s?new Set(s.notes.map(n=>n.pc)):null;}

function draw(){if(!el.map)return;const cv=el.map,[g,w,hh]=fit(cv),C=cols(),live=isLive();g.clearRect(0,0,w,hh);
  const tk=live?T.live:cur;
  if(!tk){g.fillStyle=C.muted;g.font=`500 10.5px ${C.mono}`;g.textAlign='center';if('letterSpacing' in g)g.letterSpacing='1px';
    g.fillText('PRESS REC AND PLAY · THE MAP DRAWS HERE',w/2,hh/2+4);if('letterSpacing' in g)g.letterSpacing='0px';return;}
  const a=live?null:analysis(),G=GUT(),gr=live?gridOf({bpm:tk.bpm,sig:tk.sig,t0:0}):a.g,gridOn=!live||tk.grid==='metro',detail=live?'notes':S.detail;
  let V=viewOf();const pp=T.mode==='play'?playPos():null;if(pp!=null&&S.view!=='fit'){follow(pp,V);V=viewOf();}
  const X=t=>G+(t-V.a)/(V.b-V.a)*(w-G-PR),tNow=live&&T.mode==='rec'?relT(now()):0;
  let top=RUL;const formY=top;if(detail==='form')top+=FORM_H;const chY=top;if(detail!=='notes')top+=CH_H;top+=4;
  const bot=hh-6,rows=live?[...new Set(tk.notes.map(n=>n.m))].sort((p,q)=>q-p):a.rows,nR=Math.max(1,rows.length),rh=Math.min(14,(bot-top)/nR),y0=top+((bot-top)-rh*nR)/2;
  const rowY=new Map(rows.map((m,i)=>[m,y0+i*rh]));
  draw.geo={G,V,w,hh,top,bot,rows,rh,y0,formY,chY,detail};
  g.save();g.beginPath();g.rect(G-1,0,w-G-PR+2,hh);g.clip();g.lineWidth=1;
  // ---- time grid: thin bar lines, a stronger one every four bars ----
  if(gridOn){const b0=Math.floor((V.a-gr.t0)/gr.bar),b1=Math.ceil((V.b-gr.t0)/gr.bar),ppb=(w-G-PR)/((V.b-V.a)/gr.bar);
    if(detail==='notes'&&ppb/gr.num>=22){g.strokeStyle=C.line;g.globalAlpha=0.45;g.beginPath();
      for(let b=b0;b<b1;b++)for(let i=1;i<gr.num;i++){const x=Math.round(X(gr.t0+b*gr.bar+i*gr.beat))+0.5;g.moveTo(x,top);g.lineTo(x,bot);}g.stroke();g.globalAlpha=1;}
    g.font=`500 9.5px ${C.mono}`;g.textAlign='left';
    for(let b=b0;b<=b1;b++){const x=Math.round(X(gr.t0+b*gr.bar))+0.5,strong=mod(b,4)===0;
      g.strokeStyle=strong?C.muted:C.line;g.globalAlpha=strong?0.8:1;g.beginPath();g.moveTo(x,strong?0:RUL-4);g.lineTo(x,hh);g.stroke();g.globalAlpha=1;
      if(b<b1&&(strong||ppb>=26)){g.fillStyle=strong?C.ink:C.muted;g.fillText(String(b+1),x+4,11);}}   // a pickup bar is bar 0
  }else{g.font=`500 9.5px ${C.mono}`;g.textAlign='left';const step=(V.b-V.a)/1000>40?10:5;
    for(let s=0;s*1000<=V.b;s+=step){const x=Math.round(X(s*1000))+0.5;g.strokeStyle=C.line;g.beginPath();g.moveTo(x,RUL-4);g.lineTo(x,hh);g.stroke();g.fillStyle=C.muted;g.fillText(s+' s',x+4,11);}}
  // ---- selected bars ----
  if(!live&&sel){const x1=X(gr.t0+sel[0]*gr.bar),x2=X(gr.t0+(sel[1]+1)*gr.bar);g.fillStyle=C.ink;g.globalAlpha=0.07;g.fillRect(x1,0,x2-x1,hh);g.globalAlpha=0.9;g.strokeStyle=C.ink;
    g.beginPath();g.moveTo(Math.round(x1)+0.5,0);g.lineTo(Math.round(x1)+0.5,hh);g.moveTo(Math.round(x2)+0.5,0);g.lineTo(Math.round(x2)+0.5,hh);g.stroke();g.globalAlpha=1;}
  // ---- Form: the four-bar phrases, lettered ----
  if(detail==='form')for(const P of a.form){const x1=X(gr.t0+P.bar0*gr.bar)+2,x2=X(gr.t0+(P.bar1+1)*gr.bar)-2;if(x2<G||x1>w)continue;
    g.strokeStyle=C.line;rr(g,x1+0.5,formY+2.5,x2-x1-1,FORM_H-6,5);g.stroke();
    g.textAlign='center';g.font=`700 14px ${C.display}`;g.fillStyle=P.label==='–'?C.muted:C.ink;const base=P.label.replace(/′+$/,''),pr=P.label.slice(base.length),cx=(Math.max(x1,G)+Math.min(x2,w-PR))/2;
    const bw=g.measureText(base).width,pw=pr?g.measureText(pr).width:0;g.fillText(base,cx-pw/2,formY+FORM_H/2+5);
    if(pr){g.fillStyle=C.accent;g.fillText(pr,cx+bw/2,formY+FORM_H/2+5);}}
  // ---- Chords: one block per chord, its symbol and its roman numeral in the selected scale ----
  if(detail!=='notes')for(const s of a.segs){const x1=X(s.a)+2,x2=X(s.b)-2;if(x2<G||x1>w||x2-x1<3)continue;
    g.strokeStyle=C.line;rr(g,x1+0.5,chY+2.5,x2-x1-1,CH_H-6,5);g.stroke();
    g.save();g.beginPath();g.rect(x1+1,chY,x2-x1-2,CH_H);g.clip();const bw=x2-x1,cx=(x1+x2)/2;
    g.font=`500 13px ${C.display}`;const sw=g.measureText(s.sym).width,fits=sw<=bw-8;g.textAlign=fits?'center':'left';g.fillStyle=C.ink;g.fillText(s.sym,fits?cx:x1+4,chY+17);
    g.font=`500 10.5px ${C.mono}`;const rw=g.measureText(s.roman).width,rf=rw<=bw-8;g.textAlign=rf?'center':'left';g.fillStyle=C.accent;g.fillText(s.roman,rf?cx:x1+4,chY+31);g.restore();}
  // ---- notes: one row per pitch played; grey = in the scale, pink = outside it; in Chords, coloured by role in the chord ----
  const scaleSet=inScaleSet(),nh=clamp(rh-2,2,8);
  for(let i=0;i<tk.notes.length;i++){const n=tk.notes[i],y=rowY.get(n.m);if(y==null)continue;const kEnd=n.t+(n.open&&tk.down&&tk.down.get(n.m)===n?Math.max(1,tNow-n.t):n.d),sEnd=n.open?Math.max(kEnd,tNow):n.t+Math.max(n.s,n.d);
    const x1=X(n.t),xk=X(kEnd),xs=X(sEnd);if(xs<G||x1>w)continue;
    const out=scaleSet&&!scaleSet.has(mod(n.m,12)),role=detail==='chords'&&a?a.roles[i]:null,al=(0.5+0.5*n.v/127)*(detail==='form'&&!out?0.7:1),yy=y+(rh-nh)/2;
    g.fillStyle=role?C[role]:out?C.outscale:C.inscale;
    if(xs>xk+1){g.globalAlpha=al*0.4;g.fillRect(xk,yy+nh/2-1,xs-xk,2);}   // the pedal's tail: a thin line after the key came up
    g.globalAlpha=al;rr(g,x1,yy,Math.max(2,xk-x1-1),nh,Math.min(2,nh/2));g.fill();}
  g.globalAlpha=1;
  // ---- playhead ----
  const head=pp!=null?pp:(live&&T.mode==='rec'?tNow:null);
  if(head!=null){const x=Math.round(X(head))+0.5;g.strokeStyle=C.live;g.beginPath();g.moveTo(x,0);g.lineTo(x,hh);g.stroke();}
  g.restore();
  // ---- note names at the left edge ----
  if(S.names&&rows.length){g.font=`500 9px ${C.mono}`;g.textAlign='right';g.fillStyle=C.muted;const ton=(H.scale()||H.key())?.tonic.pc,every=rh>=9;let lastY=-99;
    rows.forEach((m,i)=>{const y=y0+i*rh+rh/2+3;if(!every&&!(mod(m,12)===ton||i===0||i===rows.length-1))return;if(y-lastY<9)return;lastY=y;
      g.fillStyle=mod(m,12)===ton?C.accent:C.muted;g.fillText(H.noteName(m),G-7,y);});}
}

// ---- status line, caption, library ----
const setHTML=(e,s)=>{if(e._h!==s){e._h=s;e.innerHTML=s;}};
const mmss=ms=>{const s=Math.floor(ms/1000);return Math.floor(s/60)+':'+String(s%60).padStart(2,'0');};
const barsTxt=r=>r[0]===r[1]?'bar '+(r[0]+1):`bars ${r[0]+1}–${r[1]+1}`;
function status(){const e=el.st;let s,rec=false;
  if(T.pick)s='Click the note that is beat one · Esc cancels';
  else if(T.mode==='armed'){s='● Ready · recording starts at your first note';rec=true;}
  else if(T.mode==='countin'){const L=T.live,beat=60000/L.bpm;s='Count-in · '+clamp(Math.ceil((T.origin-now())/beat-0.02),1,S.ci*L.sig[0]);rec=true;}
  else if(T.mode==='rec'){const L=T.live,t=Math.max(0,now()-T.origin);rec=true;
    s='● Recording · '+(L.grid==='metro'?'bar '+(Math.floor(t/(L.sig[0]*60000/L.bpm))+1)+' · ':'')+mmss(t)+(L.grid==='free'?' · free tempo':'');}
  else if(T.flash)s=esc(T.flash);
  else if(cur){const a=analysis(),nb=a.sp.last-Math.min(0,a.sp.first)+1;
    s=`<b>${esc(cur.name)}</b>${nb} bar${nb===1?'':'s'} · ${cur.bpm.toFixed(1)} bpm · ${cur.sig.join('/')} · ${cur.grid==='free'?'bars guessed':'on the metronome'}`+(T.mode==='play'?' · playing'+(sel?' '+barsTxt(sel):'')+(T.P?.loop?' · loop':''):'');}
  else s='No recording yet';
  e.classList.toggle('rec',rec);setHTML(e,s);}
function flash(msg){T.flash=msg;clearTimeout(T.flashT);T.flashT=setTimeout(()=>{T.flash='';status();},4000);status();}
function capIdle(){if(isLive()||!cur)return'';const a=analysis(),ch=a.segs.length,f=a.form.map(p=>p.label).join(' ');
  if(sel)return`${barsTxt(sel)} selected · click the selection to clear it`;
  return S.detail==='form'?`Form · ${f}`:S.detail==='chords'?`${ch} chord${ch===1?'':'s'} · ${a.segs.slice(0,8).map(s=>s.sym).join(' · ')}${ch>8?' …':''}`:`${cur.notes.length} notes · ${a.rows.length} different pitches`;}
function cap(t){const s=t??capIdle();if(el.cap._t!==s){el.cap._t=s;el.cap.textContent=s;}}
function renderLib(mode){   // mode: {rename:id} or {ask:id}
  if(!takes.length){el.lib.innerHTML='<span class="none">Your recordings are kept here</span>';return;}
  el.lib.innerHTML=takes.map(t=>{const on=cur&&t.id===cur.id,id=esc(t.id);
    if(mode?.ask===t.id)return`<span class="sm-tk on"><span class="ask">Delete “${esc(t.name)}”?</span><button data-yes="${id}" ${h('Delete','Deletes this recording from this browser for good.')}>Delete</button><button data-no="1" ${h('Keep','Keeps the recording.')}>Keep</button></span>`;
    if(mode?.rename===t.id)return`<span class="sm-tk on"><input id="smName" value="${esc(t.name)}" maxlength="60" aria-label="Name of the recording" ${h('Name','Type a new name and press Enter. Esc keeps the old one.')}></span>`;
    return`<span class="sm-tk${on?' on':''}"><button class="sm-tk-n" data-id="${id}" title="${esc(t.name)}">${esc(t.name)}<small>${t.bpm.toFixed(0)} bpm</small></button>`+
      (on?`<button class="sm-tk-i" data-ren="${id}" aria-label="Rename" ${h('Rename','Gives this recording a name. The MIDI file uses it too.')}>✎</button><button class="sm-tk-i" data-del="${id}" aria-label="Delete" ${h('Delete','Deletes this recording. It asks first.')}>×</button>`:'')+`</span>`;}).join('');
  const inp=el.lib.querySelector('#smName');if(inp){inp.focus();inp.select();const id=mode.rename;let done=false;
    const end=ok=>{if(done)return;done=true;const t=takes.find(x=>x.id===id),v=inp.value.trim();if(ok&&t&&v&&v!==t.name){t.name=v;saveTake(t);}renderLib();status();};
    inp.onkeydown=e=>{e.stopPropagation();if(e.key==='Enter')end(true);else if(e.key==='Escape')end(false);};inp.onblur=()=>end(true);}}
function dots(){const n=sigArr()[0];el.dots.innerHTML='<i></i>'.repeat(n);}
function dotFlash(i){const d=el.dots?.children;if(!d)return;for(let k=0;k<d.length;k++)d[k].classList.toggle('on',k===i);}
function segSet(box,v){box.querySelectorAll('button[data-v]').forEach(b=>b.classList.toggle('on',b.dataset.v===String(v)));}
function ui(){const live=isLive(),play=T.mode==='play',has=!!cur;
  el.rec.textContent=live?'■ Stop':'● Rec';el.rec.classList.toggle('on',live);
  el.play.textContent=play?'■ Stop':'▶ Play';el.play.disabled=!has||live;
  el.loop.classList.toggle('on',S.loop);el.loop.setAttribute('aria-pressed',S.loop);
  el.metro.classList.toggle('on',T.metro);el.metro.setAttribute('aria-pressed',T.metro);
  segSet(el.detail,S.detail);segSet(el.ci,S.ci);segSet(el.tick,S.tick);segSet(el.vol,S.vol);segSet(el.view,S.view);
  el.names.checked=S.names;el.pedalX.checked=S.pedalX;
  if(document.activeElement!==el.bpm)el.bpm.value=S.bpm;el.sig.value=S.sig;el.bpm.disabled=el.sig.disabled=el.tap.disabled=live;
  el.nudge.querySelectorAll('button').forEach(b=>b.disabled=!has||live);for(const b of[el.one,el.exp,el.use])b.disabled=!has||live;
  el.tval.textContent=has?cur.bpm.toFixed(1):'—';el.one.classList.toggle('on',T.pick);el.one.setAttribute('aria-pressed',T.pick);el.map.classList.toggle('pick',T.pick);
  status();cap();}
function pickSet(on){T.pick=!!on&&!!cur&&!isLive();if(el.one){el.one.classList.toggle('on',T.pick);el.map.classList.toggle('pick',T.pick);status();}}

// ---- fixing the bars of a take ----
function retime(fn){if(!cur||isLive())return;const was=T.mode==='play';if(was)playStop();fn(cur);cur.bpm=clamp(Math.round(cur.bpm*100)/100,20,400);
  const g=gridOf(cur),first=cur.notes.reduce((m,n)=>Math.min(m,n.t),Infinity);cur.t0=Math.round(barOne(cur.t0,g.bar,first,g.eps));   // bar one stays at the first note's bar, whatever the new bar length
  sel=null;saveTake(cur);layoutView();ui();draw();}
function setBeatOne(t){retime(tk=>{const g=gridOf(tk),first=tk.notes.reduce((m,n)=>Math.min(m,n.t),Infinity);tk.t0=Math.round(barOne(t,g.bar,first,g.eps));});pickSet(false);flash('Bar lines moved · that note is now beat one');}

// ---- export and progression ----
function chordList(){const a=analysis(),g=a.g,out=[];const lo=sel?sel[0]:-Infinity,hi=sel?sel[1]+1:Infinity;
  for(const s of a.segs){if(s.bar1<=lo||s.bar0>=hi)continue;const b0=Math.floor(s.bar0)+1,b1=Math.max(b0,Math.ceil(s.bar1));out.push({symbol:s.sym,roman:s.roman,bars:b0===b1?String(b0):b0+'–'+b1});}
  return out;}
function exportMidi(save=true){if(!cur)return null;const R=playRange(),key=H.scale()||H.key(),ks=keySf(key,H),name=cur.name+(sel?' · '+barsTxt(sel):'');
  const f=buildMidi(cur,{name,a:R.a,b:R.b,sf:ks.sf,mi:ks.mi,pedal:S.pedalX});
  // read the file back before saving it: same notes, tempo, time signature and name
  let ok=false,why='';try{const p=parseMidi(f.bytes),g=gridOf(cur);ok=p.format===1&&p.tracks.length===2&&p.tracks[1].notes.length===f.count&&!p.tracks[1].hung&&p.tracks[1].name===name
      &&Math.abs(60e6/p.tempo-cur.bpm*4/g.den)<0.01&&p.sig[0]===g.num&&p.sig[1]===g.den&&p.key.sf===ks.sf&&p.tracks[1].end===f.endTick;if(!ok)why='the file did not read back the same';}catch(e){why=e.message;}
  const file=name.replace(/[\\/:*?"<>|]+/g,' ').replace(/\s+/g,' ').trim()+'.mid';
  if(!ok){flash('MIDI file not saved · '+why);return{ok,file,...f};}
  if(save){const url=URL.createObjectURL(new Blob([f.bytes],{type:'audio/midi'})),a=document.createElement('a');a.href=url;a.download=file;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),4000);
    flash(`Saved ${file} · ${f.count} notes · checked`);}
  return{ok,file,...f};}

function build(root){
  if(!document.getElementById('smStyle')){const st=document.createElement('style');st.id='smStyle';st.textContent=CSS;document.head.appendChild(st);}
  root.insertAdjacentHTML('beforeend',TPL);
  const q=id=>root.querySelector('#'+id);
  Object.assign(el,{root,rec:q('smRec'),play:q('smPlay'),loop:q('smLoop'),detail:q('smDetail'),st:q('smSt'),scroll:q('smScroll'),spacer:q('smSpacer'),map:q('smMap'),cap:q('smCap'),
    metro:q('smMetro'),bpm:q('smBpm'),tap:q('smTap'),sig:q('smSig'),dots:q('smDots'),nudge:q('smNudge'),tval:q('smTval'),one:q('smOne'),exp:q('smExport'),use:q('smUse'),lib:q('smLib'),
    ci:q('smCi'),tick:q('smTick'),vol:q('smVol'),view:q('smView'),names:q('smNames'),pedalX:q('smPedalX'),optBtn:q('smOptBtn')});
  el.optBtn.addEventListener('click',e=>{e.stopPropagation();e.stopImmediatePropagation();H.optToggle?.(el.optBtn);});   // (the page wires every .opt-btn it finds too: only one of the two may run)
  const seg=(box,key,num,after)=>box.addEventListener('click',e=>{const b=e.target.closest('button[data-v]');if(!b)return;S[key]=num?+b.dataset.v:b.dataset.v;setSave();after?.();ui();draw();});
  seg(el.detail,'detail');seg(el.ci,'ci',true);seg(el.tick,'tick');seg(el.vol,'vol');seg(el.view,'view',false,layoutView);
  el.names.onchange=()=>{S.names=el.names.checked;setSave();draw();};el.pedalX.onchange=()=>{S.pedalX=el.pedalX.checked;setSave();};
  el.rec.onclick=()=>isLive()?recStop():recStart();
  el.play.onclick=()=>T.mode==='play'?playStop():playStart();
  el.loop.onclick=()=>{S.loop=!S.loop;setSave();if(T.P)T.P.loop=S.loop;ui();};
  el.metro.onclick=()=>{if(isLive())return;metroSet(!T.metro);};
  el.bpm.onchange=()=>{S.bpm=clamp(Math.round(+el.bpm.value)||S.bpm,30,300);el.bpm.value=S.bpm;setSave();};
  el.bpm.onkeydown=e=>{if(e.key==='Enter')el.bpm.blur();};
  el.sig.onchange=()=>{S.sig=el.sig.value;T.M.i=0;setSave();dots();};
  el.tap.onclick=()=>{const t=now(),a=T.taps;if(a.length&&t-a[a.length-1]>2000)a.length=0;a.push(t);if(a.length>7)a.shift();
    if(a.length>=2){S.bpm=clamp(Math.round(60000/((a[a.length-1]-a[0])/(a.length-1))),30,300);setSave();ui();if(T.metro&&T.mode==='idle'){T.M.next=t+60000/S.bpm;T.M.i=1%sigArr()[0];}}};
  el.nudge.onclick=e=>{const b=e.target.closest('button');if(!b||b.disabled)return;if(b.dataset.d)retime(tk=>{tk.bpm+=+b.dataset.d;});else if(b.dataset.f)retime(tk=>{tk.bpm*=+b.dataset.f;});};
  el.one.onclick=()=>pickSet(!T.pick);
  el.exp.onclick=()=>exportMidi(true);
  el.use.onclick=()=>{if(!cur)return;const list=chordList();if(!list.length){flash('No chords found in '+(sel?'these bars':'this take'));return;}
    H.useProgression?.({name:cur.name+(sel?' · '+barsTxt(sel):''),key:(H.key()?.label)||'',chords:list});flash(`Sent ${list.length} chord${list.length===1?'':'s'} to Progression`);};
  el.lib.addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;const d=b.dataset;
    if(d.id){const t=takes.find(x=>x.id===d.id);if(t&&t!==cur&&!isLive())select(t);}
    else if(d.ren)renderLib({rename:d.ren});else if(d.del)renderLib({ask:d.del});else if(d.no)renderLib();
    else if(d.yes){const i=takes.findIndex(x=>x.id===d.yes);if(i>=0){const t=takes[i];takes.splice(i,1);DB.del(t.id);if(cur===t)select(takes[i]||takes[i-1]||null);else renderLib();flash('Deleted');}}});
  // ---- the map: drag across bars to select; click a phrase or a chord to select its bars; click the selection to clear it ----
  const at=e=>{const r=el.map.getBoundingClientRect(),G=draw.geo;if(!G||!cur)return null;const x=e.clientX-r.left,y=e.clientY-r.top,a=analysis(),g=a.g;
    const t=G.V.a+(x-G.G)/(G.w-G.G-PR)*(G.V.b-G.V.a);return{x,y,t,bar:clamp(Math.floor((t-g.t0)/g.bar),a.sp.first,a.sp.last),a,g,G};};
  let drag=null;
  const hover=e=>{const p=at(e);if(!p||isLive()){cap();return;}const{t,y,a,g,G}=p,b=Math.floor((t-g.t0)/g.bar),beat=Math.floor(mod(t-g.t0,g.bar)/g.beat)+1,parts=[`Bar ${b+1} · beat ${beat}`];
    if(y>=G.top&&G.rows.length){const i=Math.floor((y-G.y0)/G.rh);if(i>=0&&i<G.rows.length)parts.push(H.noteName(G.rows[i]));}
    const s=a.segs.find(s=>t>=s.a&&t<s.b);if(s)parts.push(s.sym+(s.roman?' ('+s.roman+')':''));
    const P=a.form.find(P=>b>=P.bar0&&b<=P.bar1);if(P&&G.detail==='form')parts.push('phrase '+P.label+(P.like!=null&&P.sim<0.8?` · a variation of bars ${P.like*4+1}–${P.like*4+4}`:''));
    cap(parts.join(' · '));};
  el.map.addEventListener('pointerdown',e=>{if(!cur||isLive()||(e.pointerType==='mouse'&&e.button!==0))return;const p=at(e);if(!p)return;
    if(T.pick){let best=null;for(const n of cur.notes){const dx=Math.abs(n.t-p.t);if(!best||dx<best.dx)best={dx,t:n.t};}   // snap to the nearest note start, if it is close
      const pxMs=(p.G.w-p.G.G-PR)/(p.G.V.b-p.G.V.a);let t=p.t;
      if(best&&best.dx*pxMs<=14){const near=cur.notes.filter(n=>Math.abs(n.t-best.t)<=40);t=near.reduce((s,n)=>s+n.t,0)/near.length;}   // a chord: the middle of its notes
      setBeatOne(t);return;}
    drag={b0:p.bar,x:e.clientX,y:p.y,moved:false,touch:e.pointerType==='touch',was:sel?[...sel]:null};if(!drag.touch){try{el.map.setPointerCapture(e.pointerId);}catch(_){}}});
  el.map.addEventListener('pointermove',e=>{if(drag&&!drag.touch){const p=at(e);if(!p)return;if(p.bar!==drag.b0||Math.abs(e.clientX-drag.x)>4)drag.moved=true;
      if(drag.moved){sel=[Math.min(drag.b0,p.bar),Math.max(drag.b0,p.bar)];cap();draw();}return;}hover(e);});
  const up=e=>{const d=drag;drag=null;if(!d||e.type==='pointercancel')return;if(d.touch&&Math.abs(e.clientX-d.x)>8)return;
    if(!d.moved){const p=at(e);if(!p)return;const{a,G}=p;let r=[p.bar,p.bar];
      if(G.detail==='form'&&d.y>=G.formY&&d.y<G.formY+FORM_H){const P=a.form.find(P=>p.bar>=P.bar0&&p.bar<=P.bar1);if(P)r=[P.bar0,P.bar1];}
      else if(G.detail!=='notes'&&d.y>=G.chY&&d.y<G.chY+CH_H){const s=a.segs.find(s=>p.t>=s.a&&p.t<s.b);if(s)r=[Math.floor(s.bar0),Math.max(Math.floor(s.bar0),Math.ceil(s.bar1)-1)];}
      sel=d.was&&p.bar>=d.was[0]&&p.bar<=d.was[1]?null:r;}
    if(T.mode==='play')playStart();ui();draw();};
  el.map.addEventListener('pointerup',up);el.map.addEventListener('pointercancel',up);
  el.map.addEventListener('pointerleave',()=>{if(!drag)cap();});
  el.scroll.addEventListener('scroll',()=>{if(T.mode!=='play')draw();},{passive:true});
  document.addEventListener('keydown',e=>{if(e.key==='Escape'&&T.pick){pickSet(false);e.stopPropagation();}},true);
  new ResizeObserver(()=>draw()).observe(el.map);
  document.addEventListener('visibilitychange',()=>{if(!document.hidden)draw();});
  if(document.fonts?.ready)document.fonts.ready.then(()=>draw());
}

/* =====================================================================================================
   5. Public API
   ===================================================================================================== */
SM.init=async function(o){const W=window,pick=k=>o[k]??(typeof W[k]==='function'?W[k]:undefined);
  H={key:o.key||(()=>null),scale:o.scale||o.key||(()=>null),master:o.master||(()=>H.ac().destination),CHORDS:o.CHORDS,SYM:o.SYM,MODE_OFFSET:o.MODE_OFFSET||{},LPC:o.LPC||{C:0,D:2,E:4,F:5,G:7,A:9,B:11},
    detectChord:pick('detectChord'),spellPc:pick('spellPc'),romanFor:pick('romanFor'),parseDeg:pick('parseDeg'),tone:pick('tone'),ac:pick('ac'),optToggle:pick('optToggle'),useProgression:o.useProgression};
  H.noteName=m=>{const n=H.spellPc(mod(m,12));return n.name+(Math.floor((m-H.LPC[n.letter]-n.acc)/12)-1);};
  const root=o.el||document.querySelector('[data-blk="songmap"]');if(!root||el.root)return SM;
  setLoad();build(root);dots();ui();draw();
  await DB.open();takes=(await DB.all()).filter(validTake).map(unpack).sort((a,b)=>b.created-a.created);
  cur=takes.find(t=>t.id===S.cur)||takes[0]||null;layoutView();renderLib();ui();draw();SM.ready=true;return SM;};
// the page's MIDI events (t = performance.now() of the event; leave it out for "now")
SM.noteOn=function(m,v=100,tp=now()){if(!T.live)return;
  if(T.mode==='armed'){T.origin=tp;T.mode='rec';if(T.pedal){T.live.pedal=true;T.live.ped.push([0,1]);}ui();}
  else if(T.mode==='countin'){if(tp<T.origin+T.lat-150)return;}   // a note just before the downbeat counts as beat one
  else if(T.mode!=='rec')return;
  recOn(T.live,relT(tp),m,v);};
SM.noteOff=function(m,tp=now()){if(T.live&&(T.mode==='rec'||T.mode==='countin'))recOff(T.live,relT(tp),m);};
SM.pedal=function(on,tp=now()){T.pedal=!!on;if(T.live&&(T.mode==='rec'||T.mode==='countin'))recPedal(T.live,relT(tp),on);};
SM.allOff=function(){T.pedal=false;if(T.live&&T.mode==='rec')recClose(T.live,relT(now()));};
SM.refresh=function(){if(!el.root)return;const k=(H.key()?.label||'')+'|'+(H.scale()?.label||'');if(k===SM._k)return;SM._k=k;an=null;ui();draw();};
// a take from a list of timed events [{t, on:midi|off:midi|pedal:bool, v}] (tests, and a way in for other sources)
SM.importEvents=function(events,o={}){const sig=(o.sig||S.sig).split('/').map(Number),L=newLive(o.metro?'metro':'free',o.bpm||S.bpm,sig);let t0=0,end=0;
  if(!o.metro){const f=events.find(e=>e.on!=null);t0=f?f.t:0;}
  for(const e of events){const t=Math.max(0,e.t-t0);end=Math.max(end,t);if(e.on!=null)recOn(L,t,e.on,e.v??100);else if(e.off!=null)recOff(L,t,e.off);else if(e.pedal!=null)recPedal(L,t,e.pedal);}
  recClose(L,end);const tk=finish(L,o.name,o.dry);if(tk&&el.root&&!o.dry)select(tk);return tk;};   // dry: work it out, but don't keep it
SM.recStart=recStart;SM.recStop=recStop;SM.play=playStart;SM.stop=()=>{recStop();playStop();};SM.metronome=metroSet;
SM._={estimate,analyse,buildMidi,parseMidi,gridOf,spanOf,barOne,exportMidi,chordList,T,S,get takes(){return takes;},get cur(){return cur;},get sel(){return sel;},set sel(v){sel=v;ui();draw();},
  analysis,select,setBeatOne,retime,draw,get geo(){return draw.geo;}};
window.SongMap=SM;
})();

/* Tonos · Song map: a loop recorder and a chord history in one block.

   It records what the player plays (notes, timing, velocity, pedal), finds the bars and the four-bar phrases, and draws the
   take as a map at three levels of detail: Notes, Chords (the chord history) and Form (A, B, A′). It has a metronome
   tied to the selected scale, a library kept in this browser (IndexedDB), playback through the board's sound,
   bar selection + loop, MIDI-file export for Ableton, and "Use as progression".

   Integration (three touches in the page):
     1. <script src="songmap.js"></script>
     2. <section class="panel" data-blk="songmap"></section>          (plus its entry in LAY_DEF)
     3. SongMap.init({el, key:()=>key, scale:()=>scale||key, master:()=>master, CHORDS, SYM, MODE_OFFSET, LPC,
                      useProgression:p=>{…}, midiOn:()=>bool, micStart:async()=>bool});
        and feed it the events:  SongMap.noteOn(m,v,t,src) · SongMap.noteOff(m,t,src) · SongMap.pedal(on) · SongMap.allOff()
        (src is 'midi' or 'mic'; the page sends mic notes only while SongMap.wantsMic() is true)
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
// A tail counts only for notes struck in this bar (barA = where the bar starts): what still rings from the bar before does not name the new chord.
function chordIn(ns,a,b,Hh,barA=a){const w=new Map(),low=new Map(),ovl=(x,y)=>Math.max(0,Math.min(y,b)-Math.max(x,a));
  for(const n of ns){const k=n.t+Math.max(n.d,60),e=Math.max(k,n.t+n.s);if(n.t>=b||e<=a)continue;const key=ovl(n.t,k),tail=n.t>=barA-60?ovl(k,e):0;
    if(key+tail<Math.min(50,(b-a)*0.1))continue;const pc=mod(n.m,12),x=(key+0.35*tail)*(0.4+0.6*n.v/127)*(n.m<60?1:0.6);
    w.set(pc,(w.get(pc)||0)+x);if(!low.has(pc)||n.m<low.get(pc))low.set(pc,n.m);}
  if(w.size<2)return null;const all=[...w].sort((p,q)=>q[1]-p[1]),ref=all[1][1],pcs=all.filter(x=>x[1]>=0.3*ref);   // short passing notes don't count. Measured against the second strongest note, so a long or doubled bass does not push the rest of the chord out
  while(pcs.length>=2){const d=nameChord(pcs.map(x=>x[0]),low,Hh);if(d)return d;if(pcs.length<=3)break;pcs.pop();}return null;}
// the name for a set of notes: the board's own chord finder first, plus two left-hand shapes it does not name
function nameChord(pcs,low,Hh){const ms=pcs.map(p=>low.get(p)),bass=mod(Math.min(...ms),12);
  // two notes a fifth (or its mirror, a fourth) apart: a power chord on the lower note of the fifth, whichever of the two is in the bass
  if(pcs.length===2){const iv=mod(pcs[1]-pcs[0],12);if(iv===7||iv===5)return{r:iv===7?pcs[0]:pcs[1],q:'5',bass,pcs};}
  const d=Hh.detectChord(ms);if(d)return{...d,pcs};
  // root, fifth and seventh with no third (A–E–G♯): a seventh chord; the selected scale says whether its missing third is major or minor
  for(const r of[bass,...pcs.filter(p=>p!==bass)]){const S=new Set(pcs.map(p=>mod(p-r,12)));if(S.size!==3||!S.has(7)||S.has(10)===S.has(11))continue;
    const sc=Hh.scale()||Hh.key(),has=x=>!!sc&&sc.notes.some(n=>n.pc===mod(r+x,12)),minor=has(3)&&!has(4);
    return{r,q:S.has(11)?(minor?'mmaj7':'maj7'):(minor?'m7':'7'),bass,pcs,no3:true};}
  return null;}
const sameChord=(a,b)=>!!a&&!!b&&a.r===b.r&&a.q===b.q;
function chordTrack(tk,g,sp,Hh){const ns=tk.notes,raw=[],halves=g.num%2===0;
  const beats=(a,i0,i1)=>{for(let i=i0;i<i1;i++){const d=chordIn(ns,a+i*g.beat,a+(i+1)*g.beat,Hh,a);if(d)raw.push({a:a+i*g.beat,b:a+(i+1)*g.beat,d});}};
  for(let b=sp.first;b<=sp.last;b++){const a=g.t0+b*g.bar,m=a+g.bar/2,z=a+g.bar,whole=chordIn(ns,a,z,Hh);
    if(halves){const h1=chordIn(ns,a,m,Hh,a),h2=chordIn(ns,m,z,Hh,a);
      if(h1&&h2){if(sameChord(h1,h2))raw.push({a,b:z,d:h1});else raw.push({a,b:m,d:h1},{a:m,b:z,d:h2});}
      else if(whole)raw.push({a,b:z,d:whole});
      else{if(h1)raw.push({a,b:m,d:h1});else beats(a,0,g.num/2);if(h2)raw.push({a:m,b:z,d:h2});else beats(a,g.num/2,g.num);}
    }else if(whole)raw.push({a,b:z,d:whole});else beats(a,0,g.num);}
  // two notes alone say little: when the chord right after or right before holds both of them, and has the same bass note, they are that chord
  const tones=d=>new Set((Hh.CHORDS[d.q]||[]).map(t=>mod(d.r+Hh.parseDeg(t).semis,12)));
  raw.forEach((s,i)=>{if(s.d.pcs?.length!==2)return;const near=[raw[i+1],raw[i-1]].filter((x,k)=>x&&x.d.pcs?.length>2&&Math.abs(k?x.b-s.a:x.a-s.b)<1&&x.d.bass===s.d.bass&&s.d.pcs.every(p=>tones(x.d).has(p)));
    if(near.length)s.d={...near[0].d};});
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

// ---- hands: which notes the left hand played ----
// The split is the lowest note of the right hand. It is guessed by sorting the take's notes into a low group and a high group (2-means on pitch);
// null = everything sits within a ninth, so one hand. the player can move it by hand (tk.split), which wins over the guess.
function autoSplit(notes){if(!notes.length)return null;let lo=Infinity,hi=-Infinity;for(const n of notes){if(n.m<lo)lo=n.m;if(n.m>hi)hi=n.m;}if(hi-lo<9)return null;
  let c1=lo,c2=hi;for(let it=0;it<16;it++){let s1=0,n1=0,s2=0,n2=0;const mid=(c1+c2)/2;for(const n of notes){if(n.m<mid){s1+=n.m;n1++;}else{s2+=n.m;n2++;}}if(!n1||!n2)break;c1=s1/n1;c2=s2/n2;}
  return Math.ceil((c1+c2)/2);}
// ---- the trees: the take in four-bar boxes, each holding two two-bar boxes, each holding two one-bar boxes ----
// Chords on top: a box names the chord that sounds longest in it (a tie goes to the earlier one). The left hand along the bottom: a box names the note
// the left hand plays most there. A one-bar box can hold two chords or two bass notes (one per half); it then shows both, when both fit.
// Boxes stay on the bar grid, so fast changes never break the lane into slivers.
const LEVELS=[4,2,1];
function spansOf(g,sp,L){const out=[];for(let b=Math.floor(sp.first/L)*L;b<=sp.last;b+=L){const b0=Math.max(b,sp.first),b1=Math.min(b+L,sp.last+1);out.push({L,bar0:b0,bar1:b1,a:g.t0+b0*g.bar,b:g.t0+b1*g.bar});}return out;}
function chordTree(segs,g,sp){return LEVELS.map(L=>spansOf(g,sp,L).map(n=>{const w=new Map();
    for(const s of segs){const o=Math.min(s.b,n.b)-Math.max(s.a,n.a);if(o<=0)continue;const e=w.get(s.sym);if(e)e.x+=o;else w.set(s.sym,{s,x:o});}
    let best=null;for(const e of w.values())if(!best||e.x>best.x+1)best=e;if(!best)return null;   // the Map keeps time order: a tie keeps the earlier chord
    n.seg=best.s;n.key=best.s.sym;n.all=[...w.values()].map(e=>e.s);
    if(L===1){const parts=segs.filter(s=>s.a<n.b-1&&s.b>n.a+1).map(s=>({a:Math.max(s.a,n.a),b:Math.min(s.b,n.b),seg:s}));if(parts.length>1)n.parts=parts;}
    return n;}).filter(Boolean));}
// the left hand's tree: the bass line of the take. Same weighing as the chords (a held key in full, the pedal's tail for a third, louder counts more).
// A bar with nothing below the dashed line takes its lowest note instead (the guessed split can sit under a bass line that moves up): marked low.
function lhTree(tk,g,sp,split,Hh){if(split==null)return null;const below=tk.notes.filter(n=>n.m<split);if(!below.length)return null;
  const weigh=(ns,a,b,barA)=>{const w=new Map();for(const n of ns){const k=n.t+Math.max(n.d,60),e=Math.max(k,n.t+n.s);if(n.t>=b||e<=a)continue;
      const key=Math.max(0,Math.min(k,b)-Math.max(n.t,a)),tail=n.t>=barA-60?Math.max(0,Math.min(e,b)-Math.max(k,a)):0,x=(key+0.35*tail)*(0.4+0.6*n.v/127);
      if(x>0){const pc=mod(n.m,12);w.set(pc,(w.get(pc)||0)+x);}}return w;};
  const top=w=>{let best=null;for(const[pc,x]of w)if(!best||x>best.x)best={pc,x};return best&&best.x>=20?best:null;};
  const bars=new Map();
  for(let b=sp.first;b<=sp.last;b++){const a=g.t0+b*g.bar,z=a+g.bar;let ns=below,w=weigh(ns,a,z,a),low=false;
    if(!top(w)){const st=tk.notes.filter(n=>n.t>=a-g.eps&&n.t<z-g.eps);if(st.length){const m=Math.min(...st.map(n=>n.m));ns=st.filter(n=>n.m===m);w=weigh(ns,a,z,a);low=true;}}
    bars.set(b,{ns,w,low});}
  const sc=Hh.scale()||Hh.key(),DEG=['1','♭2','2','♭3','3','4','♯4','5','♭6','6','♭7','7'];
  const info=o=>{o.name=Hh.spellPc(o.pc).name;const i=sc?sc.notes.findIndex(n=>n.pc===o.pc):-1;o.out=!!sc&&i<0;
    o.deg=!sc?'':i>=0?String(sc.scaleTokens[i]).replace(/b/g,'♭').replace(/#/g,'♯'):DEG[mod(o.pc-sc.tonic.pc,12)];return o;};
  return LEVELS.map(L=>spansOf(g,sp,L).map(n=>{const w=new Map();let low=true;
    for(let b=n.bar0;b<n.bar1;b++){const B=bars.get(b);for(const[pc,x]of B.w)w.set(pc,(w.get(pc)||0)+x);if(!B.low)low=false;}
    const t=top(w);if(!t)return null;n.pc=t.pc;n.key=t.pc;n.low=low;info(n);
    if(L===1&&g.num%2===0){const B=bars.get(n.bar0),m=(n.a+n.b)/2,h1=top(weigh(B.ns,n.a,m,n.a)),h2=top(weigh(B.ns,m,n.b,n.a));
      if(h1&&h2&&h1.pc!==h2.pc)n.parts=[info({a:n.a,b:m,pc:h1.pc}),info({a:m,b:n.b,pc:h2.pc})];}
    return n;}).filter(Boolean));}
// the colour a note wears (Song map ⚙ · Colours). role: its job in the chord sounding there (root, third, fifth, seventh, tension), so it changes with the chord.
// degree: its degree in the selected scale, read like the scale's home chord (1 root, 3 third, 5 fifth, 7 seventh, 2 4 6 tension), so a note keeps one colour
// all take long. 'out' = outside the scale (pink); null = no colour (grey).
function degRole(pc,Hh){const sc=Hh.scale()||Hh.key();if(!sc)return null;const i=sc.notes.findIndex(n=>n.pc===mod(pc,12));if(i<0)return'out';
  const d=parseInt(String(sc.scaleTokens[i]).replace(/[^0-9]/g,''),10);return d===1?'root':d===3?'third':d===5?'fifth':d===7?'seventh':'tension';}

function analyse(tk,Hh){const g=gridOf(tk),sp=spanOf(tk),segs=chordTrack(tk,g,sp,Hh),form=formOf(tk,g,sp,segs),split=tk.split??autoSplit(tk.notes),ct=chordTree(segs,g,sp),lt=lhTree(tk,g,sp,split,Hh);
  const roles=[];let si=0;const order=tk.notes.map((n,i)=>i).sort((a,b)=>tk.notes[a].t-tk.notes[b].t);
  for(const i of order){const n=tk.notes[i],t=n.t+g.eps;while(si<segs.length&&segs[si].b<=t)si++;const s=segs[si];roles[i]=s&&s.a<=t?roleIn(s.d,n.m,Hh):null;}
  return{g,sp,segs,form,roles,split,ct,lt,rows:[...new Set(tk.notes.map(n=>n.m))].sort((a,b)=>b-a)};}

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
const DEF={detail:'chords',zoom:0,loop:false,names:true,hands:true,pedalX:true,bpm:96,sig:'4/4',ci:4,tick:'tick',voice:'marimba',vol:'medium',input:'auto',recMetro:true,autoMidi:true,cur:'',tree:'m',colour:'degree'};
const OK={detail:['notes','chords'],tree:['s','m','l'],colour:['role','degree'],   // (the Form view, lettered phrases, is switched off: the player did not like it; its drawing code is still below)
  sig:SIGS,ci:[0,1,2,4],tick:['tick','fifth'],voice:['marimba','wood'],vol:['soft','medium','loud'],input:['auto','midi','mic']};
const S={...DEF};
function setLoad(){let old=true,oldC=true;try{const s=JSON.parse(localStorage.getItem(SET_KEY));if(s&&s.v===VERSION){old=s.ciV!==2;oldC=s.colV!==1;for(const k in DEF)if(typeof s[k]===typeof DEF[k]&&(!OK[k]||OK[k].includes(s[k])))S[k]=s[k];}}catch(e){}
  if(oldC)S.colour='degree';   // the player chose Scale degree as the colour rule (2026-11-15): settings saved before that move to it once
  if(old)S.ci=4;   // the player asked for four bars of count-in (2026-11-15): settings saved before that move to it once; after that his own choice stays
  S.bpm=clamp(Math.round(S.bpm)||96,30,300);S.zoom=S.zoom>0?clamp(S.zoom,1,512):0;}
function setSave(){try{localStorage.setItem(SET_KEY,JSON.stringify({v:VERSION,ciV:2,colV:1,...S}));}catch(e){}}
const sigArr=()=>S.sig.split('/').map(Number);

let takes=[],cur=null,sel=null,an=null,anKey='',vOff=0;   // vOff = how many bars the map is moved along when it is zoomed in   // sel = [first bar, last bar] (0 = bar one), or null
const r1=x=>Math.round(x);
const pack=tk=>({v:VERSION,id:tk.id,name:tk.name,created:tk.created,bpm:tk.bpm,sig:tk.sig,t0:tk.t0,grid:tk.grid,key:tk.key,src:tk.src||'midi',file:tk.file||'',hs:tk.split??null,
  n:tk.notes.map(n=>[r1(n.t),n.m,r1(n.d),n.v,r1(n.s)]),p:tk.ped});
const unpack=r=>({id:r.id,name:r.name,created:r.created,bpm:r.bpm,sig:r.sig,t0:r.t0,grid:r.grid,key:r.key||'',src:r.src==='mic'?'mic':'midi',file:r.file||'',split:Number.isInteger(r.hs)?r.hs:undefined,
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
// The folder for MIDI files. the player picks it once (a folder inside Google Drive works: Drive for desktop shows it as a normal folder) and Chrome lets the page
// write files straight into it. The folder's handle is remembered in a small database of its own; Chrome may ask again for permission on a later visit.
const KV={db:null,
  open(){return new Promise(res=>{if(KV.db)return res(true);try{const r=indexedDB.open('tonos-songmap-kv',1);r.onupgradeneeded=()=>r.result.createObjectStore('kv');
    r.onsuccess=()=>{KV.db=r.result;res(true);};r.onerror=r.onblocked=()=>res(false);}catch(e){res(false);}});},
  async tx(mode,fn){if(!await KV.open())return null;return new Promise(res=>{try{const t=KV.db.transaction('kv',mode),q=fn(t.objectStore('kv'));t.oncomplete=()=>res(q?q.result:true);t.onerror=t.onabort=()=>res(null);}catch(e){res(null);}});},
  get:k=>KV.tx('readonly',s=>s.get(k)),set:(k,v)=>KV.tx('readwrite',s=>s.put(v,k)),del:k=>KV.tx('readwrite',s=>s.delete(k))};
const FS={dir:null,can:()=>typeof window.showDirectoryPicker==='function',
  async load(){try{const d=await KV.get('midiDir');FS.dir=d&&d.kind==='directory'?d:null;}catch(e){FS.dir=null;}},
  async choose(){try{FS.dir=await window.showDirectoryPicker({id:'tonos-midi',mode:'readwrite'});await KV.set('midiDir',FS.dir);return true;}catch(e){return false;}},   // false: cancelled
  async forget(){FS.dir=null;await KV.del('midiDir');},
  // may the page write there? ask=true asks Chrome's permission, which only works right after a click
  async ready(ask){if(!FS.dir)return false;try{const o={mode:'readwrite'};if(await FS.dir.queryPermission(o)==='granted')return true;return!!ask&&await FS.dir.requestPermission(o)==='granted';}catch(e){return false;}},
  async write(name,bytes){const fh=await FS.dir.getFileHandle(name,{create:true}),w=await fh.createWritable();await w.write(bytes);await w.close();},
  async remove(name){try{await FS.dir.removeEntry(name);}catch(e){}}};
function analysis(){if(!cur)return null;const k=[cur.id,cur.bpm,cur.t0,cur.sig,cur.notes.length,cur.split,H.key()?.label,H.scale()?.label].join('|');
  if(k!==anKey||!an){an=analyse(cur,H);anKey=k;}return an;}
function select(tk){cur=tk||null;sel=null;an=null;vOff=0;S.cur=cur?cur.id:'';T.flash='';setSave();if(T.mode==='play')playStop();layoutView();ui();renderLib();draw();}
function saveTake(tk){an=null;return DB.put(tk);}

/* =====================================================================================================
   3. Transport: metronome, recording, playback (one clock: performance.now(); sound is scheduled a little ahead)
   ===================================================================================================== */
const T={mode:'idle',metro:false,origin:0,lat:0,live:null,P:null,M:{next:0,i:0},timer:0,raf:0,pick:false,pedal:false,flash:'',flashT:0,taps:[]};
const isLive=()=>T.mode==='armed'||T.mode==='countin'||T.mode==='rec';
const audioAt=tp=>{const c=H.ac();return Math.max(c.currentTime,c.currentTime+(tp-now())/1000);};
const latency=()=>{try{const c=H.ac();return clamp(((c.outputLatency||0)+(c.baseLatency||0))*1000,0,300);}catch(e){return 0;}};
const tonicMidi=()=>{const k=H.scale()||H.key(),pc=k?k.tonic.pc:0;return 72+pc-(pc>6?12:0);};   // G4 … F♯5
// The metronome's two voices. Marimba: a sine with a 4 ms attack that falls 40 dB in a quarter of a second, a quieter partial two octaves up
// (4×, the marimba bar's first overtone) that dies faster, and a tiny 10× knock for the mallet. Wood block: a short, dry, unpitched knock.
const hzOf=m=>440*2**((m-69)/12);
function strike(parts,at,g){const c=H.ac(),out=H.master();for(const[f,a,d]of parts){if(f>12000)continue;const o=c.createOscillator(),e=c.createGain();o.type='sine';o.frequency.value=f;
    e.gain.setValueAtTime(0.0001,at);e.gain.exponentialRampToValueAtTime(g*a,at+0.004);e.gain.exponentialRampToValueAtTime(g*a*0.01,at+d);e.gain.linearRampToValueAtTime(0,at+d+0.02);   // d = the time to fall 40 dB
    o.connect(e).connect(out);o.start(at);o.stop(at+d+0.03);}}
const mallet=(m,at,g,dur)=>{const f=hzOf(m);strike([[f,1,dur],[f*4,0.22,dur*0.3],[f*10,0.07,0.03]],at,g);};
const woodblock=(f,at,g)=>strike([[f,1,0.06],[f*2.76,0.35,0.03]],at,g);
// Marimba: beat one sounds the home note of the selected scale; the other beats a softer, shorter tap of the same note, or the fifth.
function click(tp,i){try{const at=audioAt(tp),vol={soft:0.5,medium:1,loud:1.8}[S.vol],ton=tonicMidi();
    // while a take records from the microphone the metronome is always the wood block: too short and too dry for the mic to take it for a note
    if(S.voice==='wood'||(isLive()&&T.live.src!=='midi'))woodblock(i===0?1320:880,at,(i===0?0.3:0.15)*vol);
    else if(i===0)mallet(ton,at,0.34*vol,0.26);else if(S.tick==='fifth')mallet(ton+7,at,0.17*vol,0.2);else mallet(ton,at,0.13*vol,0.14);}catch(e){}
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
// src: where the notes come from: 'midi', 'mic', or 'any' (the first note decides)
const newLive=(grid,bpm,sig,src='midi')=>({grid,bpm,sig,src,notes:[],ped:[],down:new Map(),sus:[],pedal:false});
const relT=tp=>Math.max(0,tp-T.origin-(T.live.grid==='metro'?T.lat:0));
function nextName(){let n=0;for(const t of takes){const m=/^Take (\d+)$/.exec(t.name);if(m)n=Math.max(n,+m[1]);}return'Take '+(n+1);}
function finish(L,name,dry){let notes=L.notes.map(n=>({t:n.t,m:n.m,d:n.d,s:Math.max(n.s,n.d),v:n.v})).sort((a,b)=>a.t-b.t||a.m-b.m);
  if(!notes.length)return null;
  const tk={id:'t'+Date.now().toString(36)+Math.floor(Math.random()*1296).toString(36),name:name||nextName(),created:Date.now(),bpm:L.bpm,sig:L.sig,t0:0,grid:L.grid,
    key:H.key()?.label||'',src:L.src==='mic'?'mic':'midi',notes,ped:L.ped};
  if(L.grid==='free'){const e=estimate(notes,L.sig[0],H);if(e){tk.bpm=e.bpm;tk.t0=e.t0;}}   // too few notes to guess: the metronome's tempo, bar one at the first note
  if(!dry){takes.unshift(tk);saveTake(tk);}return tk;}
// Record from: Auto = the MIDI keyboard when one is connected, otherwise whatever plays first (keyboard or mic); or MIDI / Mic by choice.
async function recStart(){if(T.mode==='play')playStop();if(T.mode!=='idle'||T.starting)return;pickSet(false);const sig=sigArr();
  if(S.autoMidi&&FS.dir)FS.ready(true);   // while the click still counts: Chrome's OK to write the take's MIDI file later
  let src=S.input==='auto'?(H.midiOn?.()?'midi':'any'):S.input;
  if(src!=='midi'){T.starting=true;let ok=false;try{ok=!!(await H.micStart?.());}catch(e){}T.starting=false;if(T.mode!=='idle')return;
    if(!ok){if(src==='mic'){flash('The microphone is not listening · allow it in Chrome, or record from MIDI');return;}src='midi';}}
  if(S.recMetro&&!T.metro){T.metroAuto=true;metroSet(true);}   // Rec starts the metronome (and recStop puts it back), unless that is switched off in the options
  T.live=newLive(T.metro?'metro':'free',S.bpm,sig,src);
  if(T.metro){try{H.ac();}catch(e){}T.lat=latency();const beat=60000/S.bpm;
    T.M.next=now()+120;T.M.i=0;T.origin=T.M.next+S.ci*sig[0]*beat;T.mode=S.ci?'countin':'rec';}
  else{T.lat=0;T.origin=0;T.mode='armed';}
  if(T.pedal&&T.mode!=='armed'&&src!=='mic'){T.live.pedal=true;T.live.ped.push([0,1]);}
  vOff=0;engineOn();loopOn();layoutView();ui();draw();}
function recStop(){if(!isLive())return;const L=T.live,armed=T.mode!=='rec'&&!L.notes.length,tEnd=armed?0:relT(now());T.mode='idle';T.live=null;
  if(!armed)recClose(L,tEnd);const tk=armed?null:finish(L);
  if(T.metroAuto){T.metroAuto=false;metroSet(false);}else if(T.metro){T.M.next=now()+60000/S.bpm;T.M.i=0;}engineOff();
  if(tk){select(tk);flash(tk.grid==='free'?`Saved · tempo guessed at ${tk.bpm.toFixed(1)} bpm`:'Saved');autoSave(tk,1200);}else{flash('Nothing recorded');layoutView();ui();draw();}}

// ---- playback through the board's sound; with a selection it plays those bars, and loops them when Loop is on ----
function playRange(){const a=analysis(),g=a.g,b0=sel?sel[0]:a.sp.first,b1=sel?sel[1]:a.sp.last;return{a:g.t0+b0*g.bar,b:g.t0+(b1+1)*g.bar};}
function playStart(){if(!cur||isLive())return;if(T.mode==='play')playStop();pickSet(false);const a=analysis(),g=a.g,R=playRange(),ev=[];
  for(const n of cur.notes)if(n.t>=R.a-g.eps&&n.t<R.b-g.eps)ev.push({t:Math.max(0,n.t-R.a),m:n.m,rel:Math.max(0.08,Math.max(n.s,n.d)/1000),g:0.05+0.14*n.v/127});   // rel = when the note was let go (key or pedal)
  const cl=[];for(let j=Math.ceil((R.a-g.t0)/g.beat-1e-6);g.t0+j*g.beat<R.b-1;j++)cl.push({t:g.t0+j*g.beat-R.a,i:mod(j,g.num)});
  try{H.ac();}catch(e){}T.P={a:R.a,len:R.b-R.a,origin:now()+90,sv:0,loop:S.loop,ev,cl};T.mode='play';engineOn();loopOn();ui();}
// notes sound with the board's own piano voice: its usual 2.4 s ring, let go where each note ended
function playSched(t,LA){const P=T.P,vEnd=t-P.origin+LA;
  while(P.sv<vEnd){const k=Math.floor(P.sv/P.len+1e-9);if(k>0&&!P.loop)break;const base=k*P.len,x0=P.sv-base,x1=Math.min(vEnd-base,P.len);
    for(const e of P.ev)if(e.t>=x0&&e.t<x1){try{H.tone(e.m,audioAt(P.origin+base+e.t),2.4,e.g,e.rel);}catch(_){}}
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
.sm-scroll{overflow:hidden;border:1px solid var(--line);border-radius:8px}
.sm-scroll canvas{display:block;width:100%;height:240px;touch-action:pan-y;cursor:crosshair}
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
.sm-dir{max-width:18ch;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
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
<h2 ${h('Song map','Records what you play and draws it as a map of the song: bars across, one row for each note you used. The same take can be read as notes or as chords.')}>Song map</h2>
<button class="opt-btn" id="smOptBtn" data-pop="smOpts" aria-label="Song map options" aria-haspopup="true" aria-expanded="false" title="Song map options" ${h('Options','Where the recording comes from (MIDI keyboard or microphone), the metronome\'s count-in, sound and volume, how many bars the map shows across, and where the MIDI files go. Your choices are remembered in this browser.')}>⚙</button>
<div class="opt-pop" id="smOpts" role="group" aria-label="Song map options">
  <div class="opt-h">Recording</div>
  <span class="tl" ${h('Record from','Where the notes come from. Auto: the MIDI keyboard when one is connected; with none, whatever plays first, keyboard or microphone. MIDI: only the keyboard. Mic: only what the microphone hears, for an acoustic piano, another instrument or your voice. The mic hears one note at a time or a simple chord, a little later and less exactly than MIDI, and no pedal.')}>Record from<span class="seg" id="smInput" role="group" aria-label="Record from"><button data-v="auto">Auto</button><button data-v="midi">MIDI</button><button data-v="mic">Mic</button></span></span>
  <label class="toggle" ${h('Rec starts the metronome','On: pressing Rec turns the metronome on by itself, counts in, and every bar lands exactly on the grid; when you stop, the metronome goes back to how it was. Off: Rec leaves the metronome alone, so with it off you play freely and the bars are worked out afterwards.')}><input type="checkbox" id="smRecMetro"> Rec starts the metronome</label>
  <div class="opt-h">Metronome</div>
  <span class="tl" ${h('Count-in','How many bars the metronome counts before the recording starts: with 4 bars you hear 1 2 3 4 four times, and the next beat one is where the recording begins. Off starts recording at once.')}>Count-in<span class="seg" id="smCi" role="group" aria-label="Count-in"><button data-v="0">Off</button><button data-v="1">1 bar</button><button data-v="2">2 bars</button><button data-v="4">4 bars</button></span></span>
  <span class="tl" ${h('Metronome · sound','Marimba: a soft wooden note, the home note of the selected scale on beat one. Wood block: a short dry knock with no pitch, higher on beat one. While you record from the microphone it is always the wood block, so the mic does not take the metronome for a note; headphones are safer still.')}>Sound<span class="seg" id="smVoice" role="group" aria-label="Metronome sound"><button data-v="marimba">Marimba</button><button data-v="wood">Wood block</button></span></span>
  <span class="tl" ${h('Metronome · other beats','With the marimba, beat one always sounds the home note of the selected scale. The other beats can be a softer, shorter tap of the same note, or the fifth of the scale. The wood block ignores this.')}>Other beats<span class="seg" id="smTick" role="group" aria-label="Sound of the other beats"><button data-v="tick">Soft</button><button data-v="fifth">Fifth</button></span></span>
  <span class="tl" ${h('Metronome · volume','How loud the metronome is. It does not change the recording.')}>Volume<span class="seg" id="smVol" role="group" aria-label="Metronome volume"><button data-v="soft">Soft</button><button data-v="medium">Medium</button><button data-v="loud">Loud</button></span></span>
  <div class="opt-h">Map</div>
  <span class="tl" ${h('Map · zoom','Zooms the map in or out around its middle. On the map itself, scroll or pinch to zoom where the pointer is, and swipe sideways (or hold Shift and scroll) to move along. Fit, or a double-click on the map, shows the whole take again. The zoom is remembered.')}>Zoom<span class="seg" id="smZoom" role="group" aria-label="Map zoom"><button data-z="out" aria-label="Zoom out">−</button><button data-z="in" aria-label="Zoom in">+</button><button data-z="fit">Fit</button></span></span>
  <label class="toggle" ${h('Map · note names','Shows the name of each row\'s note at the left edge of the map, spelled in the selected scale.')}><input type="checkbox" id="smNames"> note names</label>
  <label class="toggle" ${h('Map · hands','Splits the notes into right and left hand with a dashed line (R above, L below, in the margin), and (in Chords) adds the left hand\'s tree along the bottom of the map: the note it plays most in every four bars, two bars and bar, with its degree in the selected scale. That is the bass line of the take. A bar with nothing below the line shows its lowest note. The split is guessed from the take; drag the dashed line up or down to move it, double-click it to go back to the guess.')}><input type="checkbox" id="smHands"> hands · left-hand notes</label>
  <span class="tl" ${h('Map · colours','What a note\'s colour means in the Chords view, on the map and on the left hand\'s letters alike. Chord role: its job in the chord sounding there (salmon root, gold third, teal fifth, lavender seventh, mint a colour note), so the same note changes colour when the chord changes. Scale degree: its degree in the selected scale, read the same way (salmon 1, gold 3, teal 5, lavender 7, mint 2 4 6, pink outside the scale), so a note keeps one colour all take long.')}>Colours<span class="seg" id="smColour" role="group" aria-label="Note colours"><button data-v="degree">Scale degree</button><button data-v="role">Chord role</button></span></span>
  <span class="tl" ${h('Map · tree height','How tall the chord tree on top and the left hand\'s tree along the bottom are. Each tree has three rows: four bars, two bars, one bar. Small shows only the names; Medium adds the numeral or degree beside a name where it fits; Large puts it underneath. The block keeps its size: the notes get the rest.')}>Tree<span class="seg" id="smTree" role="group" aria-label="Tree height"><button data-v="s">Small</button><button data-v="m">Medium</button><button data-v="l">Large</button></span></span>
  <div class="opt-h">MIDI file</div>
  <span class="tl" ${h('MIDI file · folder','Pick a folder once, for example one inside your Google Drive, and the MIDI files are written straight into it instead of Downloads. From there you can drag them into Ableton. The × stops using the folder; the files in it stay.')}>Folder<span class="tl"><button class="tool sm-dir" id="smDir">Choose…</button><button class="tool" id="smDirX" aria-label="Stop using this folder">×</button></span></span>
  <label class="toggle" ${h('MIDI file · save every take','With a folder chosen, every new take is saved there as a MIDI file by itself, and saved again when you rename it or fix its bars. Off: only the MIDI file button saves.')}><input type="checkbox" id="smAuto"> save every take there</label>
  <label class="toggle" ${h('MIDI file · pedal','Writes your sustain-pedal moves into the MIDI file, so the clip in Ableton rings like your playing.')}><input type="checkbox" id="smPedalX"> include the pedal</label>
</div>
<div class="sm">
  <div class="sm-row">
    <button class="sm-main" id="smRec" ${h('Record','Starts recording what you play, on the MIDI keyboard or through the microphone (⚙ · Record from). It turns the metronome on, counts in, and the bars are exact. To play freely instead, switch off “Rec starts the metronome” in ⚙: recording then starts at your first note and the bars are worked out afterwards. Press again to stop and save.')}>● Rec</button>
    <button class="sm-main" id="smPlay" ${h('Play','Plays the recording through the board\'s sound. If you selected bars on the map, it plays only those.')}>▶ Play</button>
    <button class="tool" id="smLoop" aria-pressed="false" ${h('Loop','Repeats the selected bars (or the whole take) until you press Stop. Good for practising over a phrase.')}>Loop</button>
    <span class="sm-sep" aria-hidden="true"></span>
    <span class="tl" ${h('Detail','How the map reads the take. Notes: every note, grey inside the selected scale and pink outside it. Chords: a tree of chords on top (four bars, then two, then one), each box with the chord that sounds longest in it and its roman numeral in the selected scale; the notes are coloured as ⚙ · Colours says. A box that repeats the one around it is faint, so the bright ones show where the harmony moves.')}>Detail<span class="seg" id="smDetail" role="group" aria-label="Detail"><button data-v="notes">Notes</button><button data-v="chords">Chords</button></span></span>
  </div>
  <div class="sm-st" id="smSt" role="status" ${h('Recording','The name of the recording on the map, with its length, tempo and time signature. While recording it shows where you are.')}></div>
  <figure class="sm-fig"><div class="sm-scroll" id="smScroll"><canvas id="smMap" aria-label="Song map" ${h('Song map','Time runs left to right. Thin lines are bars, stronger lines every four bars. Each row is one note you played. Drag across bars to select them (for Play, Loop and the MIDI file); click the selection again to clear it. Scroll or pinch to zoom in where the pointer is, swipe sideways to move along, double-click to see the whole take. The dashed line separates the hands (drag it). The trees on top (chords) and along the bottom (left hand) group the bars by four, two and one; click a box to select its bars.')}></canvas></div>
    <figcaption class="sm-cap" id="smCap"></figcaption></figure>
  <div class="sm-row">
    <button class="tool" id="smMetro" aria-pressed="false" ${h('Metronome','Turns the metronome on: a marimba (or a wood block, in ⚙). Beat one sounds the home note of the selected scale. Record with it on and every bar lands exactly on the grid.')}>Metronome</button>
    <span class="tl" ${h('Metronome · tempo','Beats per minute. Type a number or use the arrows. It is locked while recording.')}>Tempo<input class="sm-num" id="smBpm" type="number" min="30" max="300" step="1" inputmode="numeric" aria-label="Tempo in beats per minute"></span>
    <button class="tool" id="smTap" ${h('Tap tempo','Tap this button in time, four or more times, and the tempo follows your taps.')}>Tap</button>
    <select class="sm-sel" id="smSig" aria-label="Time signature" ${h('Time signature','How many beats in a bar, and which note is the beat. It sets the metronome and how new recordings are split into bars.')}>${SIGS.map(s=>`<option>${s}</option>`).join('')}</select>
    <span class="sm-dots" id="smDots" aria-hidden="true" ${h('Beat lights','One light per beat of the bar. The gold one is beat one.')}></span>
  </div>
  <div class="sm-row">
    <span class="tl" ${h('Bars · tempo of this take','Fixes the bar lines of this recording when the guess is a little off. Minus and plus move the tempo by half a beat per minute: watch the lines slide onto your notes. ½ and ×2 fix a guess that is half or double the real tempo. It never changes the notes.')}>Bars<span class="seg" id="smNudge" role="group" aria-label="Tempo of this take"><button data-d="-0.5" aria-label="Slower">−</button><b class="sm-val" id="smTval">—</b><button data-d="0.5" aria-label="Faster">+</button><button data-f="0.5">½</button><button data-f="2">×2</button></span></span>
    <button class="tool" id="smOne" aria-pressed="false" ${h('This is beat one','Press it, then click the note on the map that starts a bar. All the bar lines move so that note is beat one.')}>This is beat one</button>
    <span class="sm-sep" aria-hidden="true"></span>
    <button class="tool" id="smExport" ${h('MIDI file','Saves the take (or the selected bars) as a MIDI file with its tempo, time signature, key and name: into your MIDI folder if you chose one (⚙), otherwise into Downloads. Drag the file into a clip slot in Ableton Live.')}>MIDI file ↓</button>
    <button class="tool" id="smCut" ${h('Cut into phrases','Saves one MIDI clip for each different four-bar phrase of the take, named with a letter (A, B, A′ for a variation) and its bars. A phrase that repeats is saved once. They go into your MIDI folder if you chose one (⚙), otherwise into Downloads.')}>Cut into phrases</button>
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
const GUT=()=>S.names?36:8,PR=8,RUL=16,FORM_H=28,TREE_ROW={s:14,m:18,l:28},TREE_H=()=>3*TREE_ROW[S.tree]+2;   // a tree is three rows: four bars, two bars, one bar
// what the map shows: live → from the start, growing in steps (8, 16, 32 bars…); a take → all of it, or S.zoom bars of it starting vOff bars in
function viewOf(){if(isLive()){const L=T.live,t=T.mode==='rec'?Math.max(0,now()-T.origin):0;
    if(L.grid==='metro'){const bar=L.sig[0]*60000/L.bpm;let n=8;while(t>=n*bar)n*=2;return{a:0,b:n*bar,A:0,B:n*bar,nb:0,N:0};}
    let s=20000;while(t>=s)s*=2;return{a:0,b:s,A:0,B:s,nb:0,N:0};}
  const a=analysis(),g=a.g,A=g.t0+a.sp.first*g.bar,B=g.t0+(a.sp.last+1)*g.bar,nb=a.sp.last-a.sp.first+1,N=S.zoom>0?Math.min(S.zoom,nb):nb;
  vOff=clamp(vOff,0,nb-N);const va=A+vOff*g.bar;return{a:va,b:va+N*g.bar,A,B,nb,N,bar:g.bar};}
function layoutView(){if(isLive()||!cur)vOff=0;}
// zoom like the Spectrum: k > 1 zooms in, around the point at `at` across the map (0 = left edge, 1 = right edge); never closer than one bar, never wider than the take
function zoomBy(k,at=0.5){if(!cur||isLive())return;const V=viewOf();if(V.nb<=1)return;const c=vOff+V.N*at,N=clamp(V.N/k,1,V.nb);
  S.zoom=N>=V.nb-1e-6?0:N;vOff=c-N*at;setSave();viewOf();cap();draw();}
function zoomFit(){S.zoom=0;vOff=0;setSave();cap();draw();}
function panBy(bars){if(!cur||isLive())return;vOff+=bars;viewOf();cap();draw();}
// keep the playhead on screen: when it leaves the window, turn the page
function follow(pos,V){if(V.N>=V.nb||(pos>=V.a&&pos<V.b))return;vOff=Math.floor((pos-V.A)/(V.N*V.bar)+1e-6)*V.N;}
function inScaleSet(){const s=H.scale()||H.key();return s?new Set(s.notes.map(n=>n.pc)):null;}

function draw(){if(!el.map)return;const cv=el.map,[g,w,hh]=fit(cv),C=cols(),live=isLive();g.clearRect(0,0,w,hh);
  const tk=live?T.live:cur;
  if(!tk){g.fillStyle=C.muted;g.font=`500 10.5px ${C.mono}`;g.textAlign='center';if('letterSpacing' in g)g.letterSpacing='1px';
    g.fillText('PRESS REC AND PLAY · THE MAP DRAWS HERE',w/2,hh/2+4);if('letterSpacing' in g)g.letterSpacing='0px';return;}
  const a=live?null:analysis(),G=GUT(),gr=live?gridOf({bpm:tk.bpm,sig:tk.sig,t0:0}):a.g,gridOn=!live||tk.grid==='metro',detail=live?'notes':S.detail;
  let V=viewOf();const pp=T.mode==='play'?playPos():null;if(pp!=null&&S.zoom>0){follow(pp,V);V=viewOf();}
  const X=t=>G+(t-V.a)/(V.b-V.a)*(w-G-PR),tNow=live&&T.mode==='rec'?relT(now()):0;
  const TR=TREE_ROW[S.tree],TH=TREE_H();let top=RUL;const formY=top;if(detail==='form')top+=FORM_H;const chY=top;if(detail!=='notes')top+=TH;top+=4;
  const hands=!live&&S.hands&&a.split!=null,lane=hands&&detail!=='notes'&&!!a.lt,lhY=hh-TH-2;   // lane = the left hand's tree along the bottom
  const bot=hh-6-(lane?TH:0),rows=live?[...new Set(tk.notes.map(n=>n.m))].sort((p,q)=>q-p):a.rows,nR=Math.max(1,rows.length),rh=Math.min(14,(bot-top)/nR),y0=top+((bot-top)-rh*nR)/2;
  const rowY=new Map(rows.map((m,i)=>[m,y0+i*rh]));
  const si=hands?rows.findIndex(m=>m<a.split):-1,splitY=si>0?y0+si*rh:null;   // the dashed line between the hands sits above the left hand's highest row
  draw.geo={G,V,w,hh,top,bot,rows,rh,y0,formY,chY,detail,splitY,lane,lhY,TR,TH};
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
  // ---- the trees: four bars, two bars, one bar, nested like a treemap. Chords on top (four bars at the top edge); the left hand along the bottom,
  //      mirrored (four bars at the bottom edge), so the one-bar boxes sit next to the notes. A name is drawn whole or not at all, never cut:
  //      first a smaller size, then without its numeral or degree, then nothing (the caption still names it). A box that says the same as the box
  //      around it is drawn faint, so what stands out is where the harmony moves. ----
  const DR=Array.from({length:12},(_,pc)=>degRole(pc,H)),colOf=k=>k==='out'?C.outscale:k?C[k]:null;
  const roleAt=(pc,t,d)=>{if(S.colour==='degree')return DR[mod(pc,12)];if(d===undefined){const c=a.segs.find(c=>t>=c.a&&t<c.b);d=c?c.d:null;}return d?roleIn(d,pc,H):null;};
  const NAME_Z={s:[10.5,9.5,8.5],m:[12,11,9.5,8.5],l:[13,11.5,10,8.5]}[S.tree];
  const say=(names,sub,col,cx,ry,maxW)=>{const disp=z=>`500 ${z}px ${C.display}`,mono=z=>`500 ${z}px ${C.mono}`;g.textAlign='center';
    for(const name of[].concat(names)){if(name!==[].concat(names)[0])sub='';for(const z of NAME_Z){g.font=disp(z);const nw=g.measureText(name).width;if(nw>maxW)continue;
      if(sub&&TR>=26){g.font=mono(10);if(g.measureText(sub).width<=maxW){g.font=disp(z);g.fillStyle=col;g.fillText(name,cx,ry+TR/2-1);g.font=mono(10);g.fillStyle=C.accent;g.fillText(sub,cx,ry+TR/2+10);return true;}}
      else if(sub&&TR>=17){g.font=mono(9.5);const sw=g.measureText(sub).width;if(nw+5+sw<=maxW){const x0=cx-(nw+5+sw)/2,by=ry+TR/2+z*0.36;g.textAlign='left';
        g.font=disp(z);g.fillStyle=col;g.fillText(name,x0,by);g.font=mono(9.5);g.fillStyle=C.accent;g.fillText(sub,x0+nw+5,by);g.textAlign='center';return true;}}
      g.font=disp(z);g.fillStyle=col;g.fillText(name,cx,ry+TR/2+z*0.36);return true;}}
    return false;};
  // shorter names for a chord when the box is narrow, all still true: without the bass (E/G♯ → E), then the root and minor sign only (Amaj7 → A, C♯m7 → C♯m)
  const chordNames=sg=>{const out=[sg.sym],nb=sg.sym.replace(/\/.*$/,''),root=(nb.match(/^[A-G][♯♭#b]*/)||[nb])[0],tri=root+(/^m(?!aj)/.test(sg.d.q)?'m':'');
    if(nb!==sg.sym)out.push(nb);if(tri!==nb)out.push(tri);return out;};
  const drawTree=(tree,y0,down,chords)=>tree.forEach((lv,li)=>{const ry=y0+(down?li:2-li)*TR,yt=down?y0+li*TR+0.5:y0+0.5+1.5*li,yb=down?y0+3*TR-0.5-1.5*li:y0+(3-li)*TR-0.5;
    for(const n of lv){const x1=X(n.a)+1+li,x2=X(n.b)-1-li;if(x2<G||x1>w||x2-x1<4)continue;
      g.strokeStyle=C.line;rr(g,x1,yt,x2-x1,yb-yt,6-li);g.stroke();
      const par=li?tree[li-1].find(p=>n.bar0>=p.bar0&&n.bar0<p.bar1):null;g.globalAlpha=par&&par.key===n.key&&!n.parts?0.4:1;
      const text=(o,xa,xb)=>{const name=chords?chordNames(o.seg):o.name,sub=chords?o.seg.roman:o.deg,col=chords?C.ink:colOf(roleAt(o.pc,(o.a+o.b)/2,o===n?(a.ct[li].find(c=>c.bar0===n.bar0)?.seg.d??null):undefined))||C.ink;   // a whole box: against the chord box of the same size; half a bar: against the chord sounding there
        return say(name,sub,col,(xa+xb)/2,ry,xb-xa-4);};
      if(n.parts){const xs=n.parts.map(p=>[Math.max(x1,X(p.a)),Math.min(x2,X(p.b))]);
        // every half's name, or (when the halves are too narrow) the bar's main one across the box: never a half alone, never an empty box
        g.font=`500 ${NAME_Z[NAME_Z.length-1]}px ${C.display}`;const fit=(nm,k)=>g.measureText(nm).width<=xs[k][1]-xs[k][0]-4,short=n.parts.map(p=>chords?chordNames(p.seg).pop():p.name);
        const fitsAll=short.every(fit)&&(new Set(short).size===short.length||n.parts.every((p,k)=>fit(chords?p.seg.sym:p.name,k)));   // halves that would both shorten to the same name ("E E") read as one: the bar's name instead
        if(fitsAll){g.strokeStyle=C.line;g.setLineDash([2,3]);g.beginPath();
          for(let k=1;k<xs.length;k++){const x=Math.round(xs[k][0])+0.5;g.moveTo(x,Math.max(yt,ry)+3);g.lineTo(x,Math.min(yb,ry+TR)-3);}g.stroke();g.setLineDash([]);
          n.parts.forEach((p,k)=>text(p,xs[k][0],xs[k][1]));}
        else text(n,x1,x2);}
      else text(n,x1,x2);
      g.globalAlpha=1;}});
  if(detail!=='notes'&&a.ct)drawTree(a.ct,chY,true,true);
  // ---- notes: one row per pitch played; grey = in the scale, pink = outside it; in Chords, coloured by role in the chord ----
  const scaleSet=inScaleSet(),nh=clamp(rh-2,2,8);
  for(let i=0;i<tk.notes.length;i++){const n=tk.notes[i],y=rowY.get(n.m);if(y==null)continue;const kEnd=n.t+(n.open&&tk.down&&tk.down.get(n.m)===n?Math.max(1,tNow-n.t):n.d),sEnd=n.open?Math.max(kEnd,tNow):n.t+Math.max(n.s,n.d);
    const x1=X(n.t),xk=X(kEnd),xs=X(sEnd);if(xs<G||x1>w)continue;
    const out=scaleSet&&!scaleSet.has(mod(n.m,12)),role=detail==='chords'&&a?(S.colour==='degree'?DR[mod(n.m,12)]:a.roles[i]):null,al=(0.5+0.5*n.v/127)*(detail==='form'&&!out?0.7:1),yy=y+(rh-nh)/2;
    g.fillStyle=role?colOf(role):out?C.outscale:C.inscale;
    if(xs>xk+1){g.globalAlpha=al*0.4;g.fillRect(xk,yy+nh/2-1,xs-xk,2);}   // the pedal's tail: a thin line after the key came up
    g.globalAlpha=al;rr(g,x1,yy,Math.max(2,xk-x1-1),nh,Math.min(2,nh/2));g.fill();}
  g.globalAlpha=1;
  // ---- hands: a dashed line between right and left hand; along the bottom, the left hand's main note per bar and its degree in the scale ----
  if(splitY!=null){const y=Math.round(splitY)+0.5;g.strokeStyle=C.muted;g.globalAlpha=0.7;g.setLineDash([4,4]);g.beginPath();g.moveTo(G,y);g.lineTo(w-PR,y);g.stroke();g.setLineDash([]);g.globalAlpha=1;}
  if(lane)drawTree(a.lt,lhY,false,false);
  // ---- playhead ----
  const head=pp!=null?pp:(live&&T.mode==='rec'?tNow:null);
  if(head!=null){const x=Math.round(X(head))+0.5;g.strokeStyle=C.live;g.beginPath();g.moveTo(x,0);g.lineTo(x,hh);g.stroke();}
  g.restore();
  // ---- note names at the left edge ----
  if(S.names&&rows.length){g.font=`500 9px ${C.mono}`;g.textAlign='right';g.fillStyle=C.muted;const ton=(H.scale()||H.key())?.tonic.pc,every=rh>=9;let lastY=-99;
    rows.forEach((m,i)=>{const y=y0+i*rh+rh/2+3;if(!every&&!(mod(m,12)===ton||i===0||i===rows.length-1))return;if(y-lastY<9)return;lastY=y;
      g.fillStyle=mod(m,12)===ton?C.accent:C.muted;g.fillText(H.noteName(m),G-7,y);});}
  if(lane&&S.names){g.font=`500 8.5px ${C.mono}`;g.textAlign='right';g.fillStyle=C.muted;g.fillText('L.H.',G-7,lhY+TH/2+3);}
  // the hands' letters sit in the margin, at the left end of the dashed line, clear of the notes and of the note names
  if(splitY!=null){g.font=`600 8.5px ${C.mono}`;g.textAlign='left';g.fillStyle=C.muted;g.fillText('R',1.5,splitY-3);g.fillText('L',1.5,splitY+10);}
}

// ---- status line, caption, library ----
const setHTML=(e,s)=>{if(e._h!==s){e._h=s;e.innerHTML=s;}};
const mmss=ms=>{const s=Math.floor(ms/1000);return Math.floor(s/60)+':'+String(s%60).padStart(2,'0');};
const barsTxt=r=>r[0]===r[1]?'bar '+(r[0]+1):`bars ${r[0]+1}–${r[1]+1}`;
function status(){const e=el.st;let s,rec=false;
  if(T.pick)s='Click the note that is beat one · Esc cancels';
  else if(T.mode==='armed'){const k=T.live.src;s='● Ready · recording starts at '+(k==='mic'?'the first note the mic hears':k==='any'?'your first note · keyboard or mic':'your first note');rec=true;}
  else if(T.mode==='countin'){const L=T.live,beat=60000/L.bpm;const num=L.sig[0],tot=S.ci*num,done=tot-clamp(Math.ceil((T.origin-now())/beat-0.02),1,tot);
    s=`Count-in · ${S.ci>1?`bar ${Math.floor(done/num)+1} of ${S.ci} · `:''}beat ${done%num+1}`;rec=true;}
  else if(T.mode==='rec'){const L=T.live,t=Math.max(0,now()-T.origin);rec=true;
    s='● Recording · '+(L.grid==='metro'?'bar '+(Math.floor(t/(L.sig[0]*60000/L.bpm))+1)+' · ':'')+mmss(t)+(L.grid==='free'?' · free tempo':'')+(L.src==='mic'?' · from the mic':'');}
  else if(T.flash)s=esc(T.flash);
  else if(cur){const a=analysis(),nb=a.sp.last-Math.min(0,a.sp.first)+1;
    s=`<b>${esc(cur.name)}</b>${nb} bar${nb===1?'':'s'} · ${cur.bpm.toFixed(1)} bpm · ${cur.sig.join('/')} · ${cur.grid==='free'?'bars guessed':'on the metronome'}${cur.src==='mic'?' · from the mic':''}`+(T.mode==='play'?' · playing'+(sel?' '+barsTxt(sel):'')+(T.P?.loop?' · loop':''):'');}
  else s='No recording yet';
  e.classList.toggle('rec',rec);setHTML(e,s);}
function flash(msg){T.flash=msg;clearTimeout(T.flashT);T.flashT=setTimeout(()=>{T.flash='';status();},4000);status();}
function capIdle(){if(isLive()||!cur)return'';const a=analysis(),ch=a.segs.length,f=a.form.map(p=>p.label).join(' ');
  if(sel)return`${barsTxt(sel)} selected · click the selection to clear it`;
  const V=viewOf(),b0=a.sp.first+vOff,z=V.N<V.nb?`Bars ${Math.floor(b0+0.15)+1}–${Math.ceil(b0+V.N-0.15)} of ${V.nb} · `:'';
  return z+(S.detail==='form'?`Form · ${f}`:S.detail==='chords'?`${ch} chord${ch===1?'':'s'} · ${a.segs.slice(0,8).map(s=>s.sym).join(' · ')}${ch>8?' …':''}`:`${cur.notes.length} notes · ${a.rows.length} different pitches`);}
function cap(t){const s=t??capIdle();if(el.cap._t!==s){el.cap._t=s;el.cap.textContent=s;}}
function renderLib(mode){   // mode: {rename:id} or {ask:id}
  if(!takes.length){el.lib.innerHTML='<span class="none">Your recordings are kept here</span>';return;}
  el.lib.innerHTML=takes.map(t=>{const on=cur&&t.id===cur.id,id=esc(t.id);
    if(mode?.ask===t.id)return`<span class="sm-tk on"><span class="ask">Delete “${esc(t.name)}”?</span><button data-yes="${id}" ${h('Delete','Deletes this recording from this browser for good.')}>Delete</button><button data-no="1" ${h('Keep','Keeps the recording.')}>Keep</button></span>`;
    if(mode?.rename===t.id)return`<span class="sm-tk on"><input id="smName" value="${esc(t.name)}" maxlength="60" aria-label="Name of the recording" ${h('Name','Type a new name and press Enter. Esc keeps the old one.')}></span>`;
    return`<span class="sm-tk${on?' on':''}"><button class="sm-tk-n" data-id="${id}" title="${esc(t.name)}">${esc(t.name)}<small>${t.bpm.toFixed(0)} bpm</small></button>`+
      (on?`<button class="sm-tk-i" data-ren="${id}" aria-label="Rename" ${h('Rename','Gives this recording a name. The MIDI file uses it too.')}>✎</button><button class="sm-tk-i" data-del="${id}" aria-label="Delete" ${h('Delete','Deletes this recording. It asks first. A MIDI file already saved in your folder stays there.')}>×</button>`:'')+`</span>`;}).join('');
  const inp=el.lib.querySelector('#smName');if(inp){inp.focus();inp.select();const id=mode.rename;let done=false;
    const end=ok=>{if(done)return;done=true;const t=takes.find(x=>x.id===id),v=inp.value.trim();if(ok&&t&&v&&v!==t.name){t.name=v;saveTake(t);autoSave(t,300);}renderLib();status();};
    inp.onkeydown=e=>{e.stopPropagation();if(e.key==='Enter')end(true);else if(e.key==='Escape')end(false);};inp.onblur=()=>end(true);}}
function dots(){const n=sigArr()[0];el.dots.innerHTML='<i></i>'.repeat(n);}
function dotFlash(i){const d=el.dots?.children;if(!d)return;for(let k=0;k<d.length;k++)d[k].classList.toggle('on',k===i);}
function segSet(box,v){box.querySelectorAll('button[data-v]').forEach(b=>b.classList.toggle('on',b.dataset.v===String(v)));}
function ui(){const live=isLive(),play=T.mode==='play',has=!!cur;
  el.rec.textContent=live?'■ Stop':'● Rec';el.rec.classList.toggle('on',live);
  el.play.textContent=play?'■ Stop':'▶ Play';el.play.disabled=!has||live;
  el.loop.classList.toggle('on',S.loop);el.loop.setAttribute('aria-pressed',S.loop);
  el.metro.classList.toggle('on',T.metro);el.metro.setAttribute('aria-pressed',T.metro);
  segSet(el.detail,S.detail);segSet(el.input,S.input);segSet(el.ci,S.ci);segSet(el.tick,S.tick);segSet(el.voice,S.voice);el.tick.querySelectorAll('button').forEach(b=>b.disabled=S.voice==='wood');segSet(el.vol,S.vol);segSet(el.colour,S.colour);segSet(el.tree,S.tree);
  el.names.checked=S.names;el.hands.checked=S.hands;el.pedalX.checked=S.pedalX;el.auto.checked=S.autoMidi;el.recMetro.checked=S.recMetro;el.dir.textContent=FS.dir?FS.dir.name:FS.can()?'Choose…':'Chrome only';el.dir.title=FS.dir?FS.dir.name:'';el.dirX.disabled=!FS.dir;
  if(document.activeElement!==el.bpm)el.bpm.value=S.bpm;el.sig.value=S.sig;el.bpm.disabled=el.sig.disabled=el.tap.disabled=live;
  el.nudge.querySelectorAll('button').forEach(b=>b.disabled=!has||live);for(const b of[el.one,el.exp,el.cut,el.use])b.disabled=!has||live;
  el.tval.textContent=has?cur.bpm.toFixed(1):'—';el.one.classList.toggle('on',T.pick);el.one.setAttribute('aria-pressed',T.pick);el.map.classList.toggle('pick',T.pick);
  status();cap();}
function pickSet(on){T.pick=!!on&&!!cur&&!isLive();if(el.one){el.one.classList.toggle('on',T.pick);el.map.classList.toggle('pick',T.pick);status();}}

// ---- fixing the bars of a take ----
function retime(fn){if(!cur||isLive())return;const was=T.mode==='play';if(was)playStop();fn(cur);cur.bpm=clamp(Math.round(cur.bpm*100)/100,20,400);
  const g=gridOf(cur),first=cur.notes.reduce((m,n)=>Math.min(m,n.t),Infinity);cur.t0=Math.round(barOne(cur.t0,g.bar,first,g.eps));   // bar one stays at the first note's bar, whatever the new bar length
  sel=null;saveTake(cur);autoSave(cur,1200);layoutView();ui();draw();}
function setBeatOne(t){retime(tk=>{const g=gridOf(tk),first=tk.notes.reduce((m,n)=>Math.min(m,n.t),Infinity);tk.t0=Math.round(barOne(t,g.bar,first,g.eps));});pickSet(false);flash('Bar lines moved · that note is now beat one');}

// ---- export and progression ----
function chordList(){const a=analysis(),g=a.g,out=[];const lo=sel?sel[0]:-Infinity,hi=sel?sel[1]+1:Infinity;
  for(const s of a.segs){if(s.bar1<=lo||s.bar0>=hi)continue;const b0=Math.floor(s.bar0)+1,b1=Math.max(b0,Math.ceil(s.bar1));out.push({symbol:s.sym,roman:s.roman,bars:b0===b1?String(b0):b0+'–'+b1});}
  return out;}
// the file for a take (range = [first bar, last bar], or null for all of it), read back before anyone gets it: same notes, tempo, time signature and name
function midiFor(tk,range,label){const g=gridOf(tk),sp=spanOf(tk),b0=range?range[0]:sp.first,b1=range?range[1]:sp.last,ks=keySf(H.scale()||H.key(),H),name=tk.name+(label?' · '+label:range?' · '+barsTxt(range):'');
  const f=buildMidi(tk,{name,a:g.t0+b0*g.bar,b:g.t0+(b1+1)*g.bar,sf:ks.sf,mi:ks.mi,pedal:S.pedalX});
  let ok=false,why='';try{const p=parseMidi(f.bytes);ok=p.format===1&&p.tracks.length===2&&p.tracks[1].notes.length===f.count&&!p.tracks[1].hung&&p.tracks[1].name===name
      &&Math.abs(60e6/p.tempo-tk.bpm*4/g.den)<0.01&&p.sig[0]===g.num&&p.sig[1]===g.den&&p.key.sf===ks.sf&&p.tracks[1].end===f.endTick;if(!ok)why='the file did not read back the same';}catch(e){why=e.message;}
  return{ok,why,file:name.replace(/[\\/:*?"<>|]+/g,' ').replace(/\s+/g,' ').trim()+'.mid',...f};}
function download(f){const url=URL.createObjectURL(new Blob([f.bytes],{type:'audio/midi'})),a=document.createElement('a');a.href=url;a.download=f.file;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(url),4000);}
// writes a whole take into the folder under its name; when the name changed, the file it wrote before goes away
async function writeTake(tk,f){await FS.write(f.file,f.bytes);if(tk.file&&tk.file!==f.file)await FS.remove(tk.file);if(tk.file!==f.file){tk.file=f.file;DB.put(tk);}}
function exportMidi(save=true){if(!cur)return null;const f=midiFor(cur,sel);if(save)saveMidi(f);return f;}
// the MIDI file button: into the chosen folder, or a download when there is none (or Chrome says no)
async function saveMidi(f){const tk=cur,whole=!sel;f=f||midiFor(tk,sel);if(!f.ok){flash('MIDI file not saved · '+f.why);return f;}
  if(FS.dir&&await FS.ready(true)){try{if(whole)await writeTake(tk,f);else await FS.write(f.file,f.bytes);flash(`Saved ${f.file} in “${FS.dir.name}” · ${f.count} notes · checked`);return f;}catch(e){}}
  download(f);flash(`Saved ${f.file} to Downloads · ${f.count} notes · checked`);return f;}
// Cut into phrases: one MIDI clip for each different phrase of the form (A, B, A′…), named with its letter and bars. A phrase that repeats is saved once.
async function cutPhrases(){if(!cur||isLive())return null;const tk=cur,seen=new Set(),files=[];
  for(const P of analysis().form){if(P.label==='–'||seen.has(P.label))continue;seen.add(P.label);const r=[P.bar0,P.bar1],f=midiFor(tk,r,`${P.label} · ${barsTxt(r)}`);
    if(!f.ok){flash('Not cut · '+f.why);return null;}if(f.count)files.push({label:P.label,bars:r,...f});}
  if(!files.length){flash('No phrases to cut in this take');return null;}
  const what=`${files.length} clip${files.length===1?'':'s'} · ${files.map(x=>x.label).join(' ')}`;
  if(FS.dir&&await FS.ready(true)){try{for(const x of files)await FS.write(x.file,x.bytes);flash(`Cut into ${what} · in “${FS.dir.name}”`);return files;}catch(e){}}
  for(const x of files){download(x);await new Promise(r=>setTimeout(r,300));}flash(`Cut into ${what} · in Downloads`);return files;}
// "save every take there": a new take, a new name or moved bar lines write the take's file again, quietly
let autoT=0;
function autoSave(tk,delay=0){if(!S.autoMidi||!FS.dir||!tk)return;clearTimeout(autoT);autoT=setTimeout(async()=>{if(!takes.includes(tk))return;
  if(!await FS.ready(false)){flash(`Press MIDI file ↓ once, so Chrome lets Tonos write into “${FS.dir.name}” again`);return;}
  const f=midiFor(tk,null);if(!f.ok)return;try{await writeTake(tk,f);flash(`Saved · ${f.file} is in “${FS.dir.name}”`);}catch(e){flash(`Could not write into “${FS.dir.name}” · ${e.message||e.name}`);}},delay);}

function build(root){
  if(!document.getElementById('smStyle')){const st=document.createElement('style');st.id='smStyle';st.textContent=CSS;document.head.appendChild(st);}
  root.insertAdjacentHTML('beforeend',TPL);
  const q=id=>root.querySelector('#'+id);
  Object.assign(el,{root,rec:q('smRec'),play:q('smPlay'),loop:q('smLoop'),detail:q('smDetail'),st:q('smSt'),map:q('smMap'),cap:q('smCap'),
    metro:q('smMetro'),bpm:q('smBpm'),tap:q('smTap'),sig:q('smSig'),dots:q('smDots'),nudge:q('smNudge'),tval:q('smTval'),one:q('smOne'),exp:q('smExport'),cut:q('smCut'),use:q('smUse'),lib:q('smLib'),
    input:q('smInput'),ci:q('smCi'),tick:q('smTick'),voice:q('smVoice'),vol:q('smVol'),zoom:q('smZoom'),names:q('smNames'),hands:q('smHands'),colour:q('smColour'),tree:q('smTree'),pedalX:q('smPedalX'),dir:q('smDir'),dirX:q('smDirX'),auto:q('smAuto'),recMetro:q('smRecMetro'),optBtn:q('smOptBtn')});
  el.optBtn.addEventListener('click',e=>{e.stopPropagation();e.stopImmediatePropagation();H.optToggle?.(el.optBtn);});   // (the page wires every .opt-btn it finds too: only one of the two may run)
  const seg=(box,key,num,after)=>box.addEventListener('click',e=>{const b=e.target.closest('button[data-v]');if(!b)return;S[key]=num?+b.dataset.v:b.dataset.v;setSave();after?.();ui();draw();});
  seg(el.detail,'detail');seg(el.input,'input');seg(el.ci,'ci',true);seg(el.tick,'tick');seg(el.voice,'voice');seg(el.vol,'vol');seg(el.colour,'colour');seg(el.tree,'tree');
  el.zoom.onclick=e=>{const b=e.target.closest('button');if(!b)return;const z=b.dataset.z;z==='fit'?zoomFit():zoomBy(z==='in'?1.5:1/1.5);};
  el.names.onchange=()=>{S.names=el.names.checked;setSave();draw();};el.hands.onchange=()=>{S.hands=el.hands.checked;setSave();draw();};el.pedalX.onchange=()=>{S.pedalX=el.pedalX.checked;setSave();};
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
  el.exp.onclick=()=>{if(cur)saveMidi();};
  el.cut.onclick=()=>cutPhrases();
  el.dir.onclick=async()=>{if(!FS.can()){flash('Choosing a folder works in Chrome');return;}if(await FS.choose()){ui();flash(`MIDI files go into “${FS.dir.name}” from now on`);autoSave(cur,1500);}};
  el.dirX.onclick=async()=>{await FS.forget();ui();flash('MIDI files go to Downloads again');};
  el.auto.onchange=()=>{S.autoMidi=el.auto.checked;setSave();};
  el.recMetro.onchange=()=>{S.recMetro=el.recMetro.checked;setSave();};
  el.use.onclick=()=>{if(!cur)return;const list=chordList();if(!list.length){flash('No chords found in '+(sel?'these bars':'this take'));return;}
    H.useProgression?.({name:cur.name+(sel?' · '+barsTxt(sel):''),key:(H.key()?.label)||'',chords:list});flash(`Sent ${list.length} chord${list.length===1?'':'s'} to Progression`);};
  el.lib.addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;const d=b.dataset;
    if(d.id){const t=takes.find(x=>x.id===d.id);if(t&&t!==cur&&!isLive())select(t);}
    else if(d.ren)renderLib({rename:d.ren});else if(d.del)renderLib({ask:d.del});else if(d.no)renderLib();
    else if(d.yes){const i=takes.findIndex(x=>x.id===d.yes);if(i>=0){const t=takes[i];takes.splice(i,1);DB.del(t.id);if(cur===t)select(takes[i]||takes[i-1]||null);else renderLib();flash('Deleted');}}});
  // ---- the map: drag across bars to select; click a phrase or a chord to select its bars; click the selection to clear it ----
  const at=e=>{const r=el.map.getBoundingClientRect(),G=draw.geo;if(!G||!cur)return null;const x=e.clientX-r.left,y=e.clientY-r.top,a=analysis(),g=a.g;
    const t=G.V.a+(x-G.G)/(G.w-G.G-PR)*(G.V.b-G.V.a);return{x,y,t,bar:clamp(Math.floor((t-g.t0)/g.bar),a.sp.first,a.sp.last),a,g,G};};
  let drag=null,sdrag=false;const pts=new Map(),clicks=[];let tpan=null,pinch=null;   // touch: one finger moves the map along, two fingers pinch
  const frac=x=>{const r=el.map.getBoundingClientRect(),G=draw.geo;return clamp((x-r.left-G.G)/(G.w-G.G-PR),0,1);};
  const onSplit=p=>!!p&&p.G.splitY!=null&&p.x>=p.G.G&&Math.abs(p.y-p.G.splitY)<=5;
  // which tree box is under the pointer: the row says the size (four, two or one bar), the time says which box
  const treeAt=p=>{const G=p.G;let tree=null,li=-1;if(!G.TR)return null;
    if(G.detail!=='notes'&&p.y>=G.chY&&p.y<G.chY+G.TH){tree=p.a.ct;li=Math.floor((p.y-G.chY)/G.TR);}
    else if(G.lane&&p.y>=G.lhY&&p.y<G.lhY+G.TH){tree=p.a.lt;li=2-Math.floor((p.y-G.lhY)/G.TR);}
    if(!tree||li<0||li>2)return null;const n=tree[li].find(n=>p.t>=n.a&&p.t<n.b);return n?{n,li,chords:tree===p.a.ct}:null;};
  const RN={root:'the root',third:'the third',fifth:'the fifth',seventh:'the seventh',tension:'a colour note'};
  const treeCap=(T,p)=>{const n=T.n,sc=H.scale()||H.key(),where=barsTxt([n.bar0,n.bar1-1]);
    if(T.chords){const nm=s=>s.sym+(s.roman?' ('+s.roman+')':'');if(n.parts)return`Chords · ${where} · ${n.parts.map(q=>nm(q.seg)).join(' then ')}`;
      const others=n.all.filter(s=>s.sym!==n.seg.sym).map(s=>s.sym).filter((x,i,A)=>A.indexOf(x)===i);return`Chords · ${where} · mostly ${nm(n.seg)}${others.length?' · also '+others.join(', '):''}`;}
    const one=o=>{const ch=o===n?p.a.ct[T.li].find(c=>c.bar0===n.bar0)?.seg:p.a.segs.find(c=>(o.a+o.b)/2>=c.a&&(o.a+o.b)/2<c.b),r=ch?roleIn(ch.d,o.pc,H):null;
      return`${o.name}${o.deg&&sc?` (degree ${o.deg} of ${sc.label})`:''}${r&&ch?` · ${RN[r]} of ${ch.sym}`:''}`;};
    return`Left hand · ${where} · ${n.parts?n.parts.map(one).join(' then '):'mostly '+one(n)}${n.low?' · its lowest note (nothing below the dashed line here)':''}`;};
  const hover=e=>{const p=at(e);el.map.style.cursor=onSplit(p)&&!isLive()&&!T.pick?'ns-resize':'';if(!p||isLive()){cap();return;}
    if(onSplit(p)){cap(`Hands · the left hand is everything below ${H.noteName(p.a.split)}${cur.split==null?' (guessed)':''} · drag to move, double-click for the guess`);return;}
    {const T=treeAt(p);if(T){cap(treeCap(T,p));return;}}
    const{t,y,a,g,G}=p,b=Math.floor((t-g.t0)/g.bar),beat=Math.floor(mod(t-g.t0,g.bar)/g.beat)+1,parts=[`Bar ${b+1} · beat ${beat}`];
    if(y>=G.top&&G.rows.length){const i=Math.floor((y-G.y0)/G.rh);if(i>=0&&i<G.rows.length)parts.push(H.noteName(G.rows[i]));}
    const s=a.segs.find(s=>t>=s.a&&t<s.b);if(s)parts.push(s.sym+(s.roman?' ('+s.roman+')':''));
    const P=a.form.find(P=>b>=P.bar0&&b<=P.bar1);if(P&&G.detail==='form')parts.push('phrase '+P.label+(P.like!=null&&P.sim<0.8?` · a variation of bars ${P.like*4+1}–${P.like*4+4}`:''));
    cap(parts.join(' · '));};
  el.map.addEventListener('pointerdown',e=>{if(!cur||isLive()||(e.pointerType==='mouse'&&e.button!==0))return;const p=at(e);if(!p)return;
    if(T.pick){let best=null;for(const n of cur.notes){const dx=Math.abs(n.t-p.t);if(!best||dx<best.dx)best={dx,t:n.t};}   // snap to the nearest note start, if it is close
      const pxMs=(p.G.w-p.G.G-PR)/(p.G.V.b-p.G.V.a);let t=p.t;
      if(best&&best.dx*pxMs<=14){const near=cur.notes.filter(n=>Math.abs(n.t-best.t)<=40);t=near.reduce((s,n)=>s+n.t,0)/near.length;}   // a chord: the middle of its notes
      setBeatOne(t);return;}
    if(e.pointerType!=='touch'&&onSplit(p)){sdrag=true;try{el.map.setPointerCapture(e.pointerId);}catch(_){}return;}   // the dashed line between the hands
    drag={b0:p.bar,x:e.clientX,y:p.y,moved:false,touch:e.pointerType==='touch',was:sel?[...sel]:null};if(!drag.touch){try{el.map.setPointerCapture(e.pointerId);}catch(_){}return;}
    pts.set(e.pointerId,e.clientX);const V=viewOf();
    if(pts.size===1)tpan={x:e.clientX,off:vOff,moved:false};
    else if(pts.size===2){const[a,b]=[...pts.values()];pinch={d:Math.max(8,Math.abs(a-b)),N:V.N,c:vOff+V.N*frac((a+b)/2)};tpan=null;drag=null;}});
  el.map.addEventListener('pointermove',e=>{if(e.pointerType==='touch'){if(!pts.has(e.pointerId)||!cur)return;pts.set(e.pointerId,e.clientX);const V=viewOf(),G=draw.geo;
      if(pinch&&pts.size>=2){const[a,b]=[...pts.values()],N=clamp(pinch.N*pinch.d/Math.max(8,Math.abs(a-b)),1,V.nb);S.zoom=N>=V.nb-1e-6?0:N;vOff=pinch.c-N*frac((a+b)/2);viewOf();cap();draw();}
      else if(tpan){const dx=e.clientX-tpan.x;if(!tpan.moved&&Math.abs(dx)<6)return;tpan.moved=true;vOff=tpan.off-V.N*dx/(G.w-G.G-PR);viewOf();cap();draw();}return;}
    if(sdrag){const G=draw.geo,y=e.clientY-el.map.getBoundingClientRect().top,i=clamp(Math.round((y-G.y0)/G.rh),1,G.rows.length-1),sp=G.rows[i-1];
      if(sp!==analysis().split){cur.split=sp;draw();}cap(`Hands · the left hand is everything below ${H.noteName(sp)}`);return;}
    if(drag&&!drag.touch){const p=at(e);if(!p)return;if(p.bar!==drag.b0||Math.abs(e.clientX-drag.x)>4)drag.moved=true;
      if(drag.moved){sel=[Math.min(drag.b0,p.bar),Math.max(drag.b0,p.bar)];cap();draw();}return;}hover(e);});
  const up=e=>{if(sdrag){sdrag=false;if(cur)saveTake(cur);draw();return;}
    if(pts.delete(e.pointerId)){if(pinch){setSave();if(pts.size<2)pinch=null;}tpan=null;}
    const d=drag;drag=null;if(!d||e.type==='pointercancel')return;if(d.touch&&Math.abs(e.clientX-d.x)>8)return;
    if(!d.moved){const p=at(e);if(!p)return;const{a,G}=p;let r=[p.bar,p.bar];
      if(G.detail==='form'&&d.y>=G.formY&&d.y<G.formY+FORM_H){const P=a.form.find(P=>p.bar>=P.bar0&&p.bar<=P.bar1);if(P)r=[P.bar0,P.bar1];}
      else{const T=treeAt({...p,y:d.y});if(T)r=[T.n.bar0,T.n.bar1-1];}   // a box in a tree selects its bars
      clicks.push(d.was);if(clicks.length>2)clicks.shift();sel=d.was&&p.bar>=d.was[0]&&p.bar<=d.was[1]?null:r;}
    if(T.mode==='play')playStart();ui();draw();};
  el.map.addEventListener('pointerup',up);el.map.addEventListener('pointercancel',up);
  el.map.addEventListener('pointerleave',()=>{if(!drag)cap();});
  // wheel, like the Spectrum: zoom around the pointer (a trackpad pinch arrives as ctrl+wheel); a sideways scroll, or Shift, moves along
  el.map.addEventListener('wheel',e=>{const G=draw.geo;if(!cur||isLive()||!G)return;e.preventDefault();const r=el.map.getBoundingClientRect(),u=e.deltaMode===1?16:e.deltaMode===2?r.height:1,dx=e.deltaX*u,dy=e.deltaY*u,pw=G.w-G.G-PR;
    if(e.shiftKey||Math.abs(dx)>Math.abs(dy)){panBy(G.V.N*(Math.abs(dx)>Math.abs(dy)?dx:dy)/pw);return;}
    zoomBy(Math.exp(-dy*(e.ctrlKey?0.01:0.002)),frac(e.clientX));},{passive:false});
  // double-click: the whole take again (the two clicks it is made of don't change the selection)
  el.map.addEventListener('dblclick',e=>{if(!cur||isLive()||T.pick)return;
    if(onSplit(at(e))){if(cur.split!=null){delete cur.split;saveTake(cur);draw();flash('Hands · back to the guessed split');}return;}
    sel=clicks.length===2?clicks[0]:null;clicks.length=0;zoomFit();ui();});
  document.addEventListener('keydown',e=>{if(e.key==='Escape'&&T.pick){pickSet(false);e.stopPropagation();}},true);
  new ResizeObserver(()=>draw()).observe(el.map);
  document.addEventListener('visibilitychange',()=>{if(!document.hidden)draw();});
  if(document.fonts?.ready)document.fonts.ready.then(()=>draw());
}

/* =====================================================================================================
   5. Public API (noteOn / noteOff take a last argument 'midi' or 'mic': where the note came from)
   ===================================================================================================== */
SM.init=async function(o){const W=window,pick=k=>o[k]??(typeof W[k]==='function'?W[k]:undefined);
  H={key:o.key||(()=>null),scale:o.scale||o.key||(()=>null),master:o.master||(()=>H.ac().destination),CHORDS:o.CHORDS,SYM:o.SYM,MODE_OFFSET:o.MODE_OFFSET||{},LPC:o.LPC||{C:0,D:2,E:4,F:5,G:7,A:9,B:11},
    detectChord:pick('detectChord'),spellPc:pick('spellPc'),romanFor:pick('romanFor'),parseDeg:pick('parseDeg'),tone:pick('tone'),ac:pick('ac'),optToggle:pick('optToggle'),useProgression:o.useProgression,midiOn:o.midiOn,micStart:o.micStart};
  H.noteName=m=>{const n=H.spellPc(mod(m,12));return n.name+(Math.floor((m-H.LPC[n.letter]-n.acc)/12)-1);};
  const root=o.el||document.querySelector('[data-blk="songmap"]');if(!root||el.root)return SM;
  setLoad();build(root);dots();ui();draw();
  await FS.load();await DB.open();takes=(await DB.all()).filter(validTake).map(unpack).sort((a,b)=>b.created-a.created);
  cur=takes.find(t=>t.id===S.cur)||takes[0]||null;layoutView();renderLib();ui();draw();SM.ready=true;return SM;};
// the page's MIDI events (t = performance.now() of the event; leave it out for "now")
SM.noteOn=function(m,v=100,tp=now(),src='midi'){const L=T.live;if(!L||(L.src!=='any'&&L.src!==src))return;
  if(T.mode==='armed'){T.origin=tp;T.mode='rec';if(T.pedal&&src!=='mic'){L.pedal=true;L.ped.push([0,1]);}}
  else if(T.mode==='countin'){if(tp<T.origin+T.lat-150)return;}   // a note just before the downbeat counts as beat one
  else if(T.mode!=='rec')return;
  if(L.src==='any'){L.src=src;ui();}else if(T.mode==='rec'&&!L.notes.length)ui();   // the first note decides where this take comes from
  recOn(L,relT(tp),m,v);};
SM.noteOff=function(m,tp=now(),src='midi'){const L=T.live;if(L&&L.src===src&&(T.mode==='rec'||T.mode==='countin'))recOff(L,relT(tp),m);};
SM.pedal=function(on,tp=now()){T.pedal=!!on;const L=T.live;if(L&&L.src!=='mic'&&(T.mode==='rec'||T.mode==='countin'))recPedal(L,relT(tp),on);};
SM.allOff=function(){T.pedal=false;if(T.live&&T.live.src!=='mic'&&T.mode==='rec')recClose(T.live,relT(now()));};
SM.wantsMic=()=>isLive()&&T.live.src!=='midi';   // the page asks this before it sends what the mic hears
SM.refresh=function(){if(!el.root)return;const k=(H.key()?.label||'')+'|'+(H.scale()?.label||'');if(k===SM._k)return;SM._k=k;an=null;ui();draw();};
// a take from a list of timed events [{t, on:midi|off:midi|pedal:bool, v}] (tests, and a way in for other sources)
SM.importEvents=function(events,o={}){const sig=(o.sig||S.sig).split('/').map(Number),L=newLive(o.metro?'metro':'free',o.bpm||S.bpm,sig,o.src==='mic'?'mic':'midi');let t0=0,end=0;
  if(!o.metro){const f=events.find(e=>e.on!=null);t0=f?f.t:0;}
  for(const e of events){const t=Math.max(0,e.t-t0);end=Math.max(end,t);if(e.on!=null)recOn(L,t,e.on,e.v??100);else if(e.off!=null)recOff(L,t,e.off);else if(e.pedal!=null)recPedal(L,t,e.pedal);}
  recClose(L,end);const tk=finish(L,o.name,o.dry);if(tk&&el.root&&!o.dry)select(tk);return tk;};   // dry: work it out, but don't keep it
SM.recStart=recStart;SM.recStop=recStop;SM.play=playStart;SM.stop=()=>{recStop();playStop();};SM.metronome=metroSet;
SM._={estimate,analyse,buildMidi,parseMidi,gridOf,spanOf,barOne,exportMidi,saveMidi,cutPhrases,autoSave,FS,KV,chordList,T,S,get takes(){return takes;},get cur(){return cur;},get sel(){return sel;},set sel(v){sel=v;ui();draw();},
  analysis,select,setBeatOne,retime,draw,zoomBy,zoomFit,panBy,get vOff(){return vOff;},get geo(){return draw.geo;}};
window.SongMap=SM;
})();

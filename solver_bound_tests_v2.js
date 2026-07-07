/* ==========================================================================================
   solver_bound_tests_v2.js
   Component-isolated harness. The v1 script (solver_bound_tests.js) only ever checked the fully
   composed bound end-to-end against a brute-force oracle. That's necessary but not sufficient:
   Test 2 in v1 reported 0/144,366 DAC violations against a "targeted counterexample generator"
   that, on inspection, never actually forced the precondition DAC's collision-fix bug requires
   (two remaining slots' live scans landing on the SAME group) -- it built two DIFFERENT top
   groups per pair, so the collision-resolution branch in dacVec was dead code for that entire
   run. A 100% pass rate against a generator that never exercises the buggy branch tells you
   nothing about that branch's soundness.

   This version breaks things down so each piece is checked against an oracle that specifically
   targets its own precondition, rather than inferring "probably fine" from an aggregate pass
   rate on realistic-shaped drafts:

     A) assignMaxSumNode in isolation -- vs brute-force max-weight assignment (checked for EXACT
        equality, since it claims to be an exact DP, not merely a bound).
     B) spMaxFreeBox in isolation -- vs brute-force integer-grid search over the free box (checked
        for exact equality on integer inputs, since it also claims to find the true max spread).
     C) dacVec's collision-fix branch, FORCED to fire -- a corrected targeted generator that
        actually makes two slots' live-scan top pick collide on the same group (the real DAC
        precondition), checked against the full brute-force oracle. This is what should reproduce
        the documented ~8.5% DAC violation rate; r2Vec/h2NodeBound must stay clean on the same
        instances.
     D) Composed h2NodeBound end-to-end (kept from v1, general fuzz) as a final integration check
        -- but only AFTER A/B/C have each been validated alone.

   HOW TO RUN: node solver_bound_tests_v2.js [--trials N] [--seed N]
   ========================================================================================== */

'use strict';

// ---------- shared primitives (verbatim from the file under test) ----------
function futRatingRaw(rs){const S=rs.reduce((a,b)=>a+b,0),A=S/rs.length;let sp=0;for(const r of rs)if(r>A)sp+=r-A;return (S+sp)/rs.length;}

function dacVec(order,cand,usedGroups,pick,k){
  const v=[];const firstHit=new Map();
  for(let j=0;j<order.length;j++){
    if(j<k){v.push(pick[order[j]].rating);continue;}
    const slot=order[j],list=cand[slot];let m=0,mg=null;
    for(let i=0;i<list.length;i++){const c=list[i];if(!usedGroups.has(c._group)){m=c.rating;mg=c._group;break;}}
    v.push(m);
    if(mg!==null){const a=firstHit.get(mg);if(a)a.push(j);else firstHit.set(mg,[j]);}
  }
  for(const [g,arr] of firstHit){
    if(arr.length<2)continue;
    let w=arr[0];for(const j of arr)if(v[j]>v[w])w=j;
    for(const j of arr){
      if(j===w)continue;
      const list=cand[order[j]];let m=0;
      for(let i=0;i<list.length;i++){const c=list[i];if(c._group===g)continue;if(!usedGroups.has(c._group)){m=c.rating;break;}}
      v[j]=m;
    }
  }
  return v;
}

function r2Vec(order,cand,usedGroups,pick,k){
  const v=[];
  for(let j=0;j<order.length;j++){
    if(j<k){v.push(pick[order[j]].rating);continue;}
    const list=cand[order[j]];let m=0;
    for(const c of list){ if(!usedGroups.has(c._group)){ m=c.rating; break; } }
    v.push(m);
  }
  return v;
}

function assignMaxSumNode(remSlots,cand,usedGroups){
  const R=remSlots.length;
  const L=new Array(R),U=new Array(R);
  const groupBest=new Map();
  for(let i=0;i<R;i++){
    const list=cand[remSlots[i]];let lo=Infinity,hi=-Infinity;
    for(const c of list){
      if(usedGroups.has(c._group))continue;
      if(c.rating>hi)hi=c.rating;
      if(c.rating<lo)lo=c.rating;
      let arr=groupBest.get(c._group);
      if(!arr){arr=new Array(R).fill(-Infinity);groupBest.set(c._group,arr);}
      if(c.rating>arr[i])arr[i]=c.rating;
    }
    if(hi===-Infinity)return null;
    L[i]=lo;U[i]=hi;
  }
  const full=(1<<R)-1;
  let dp=new Array(1<<R).fill(-Infinity);dp[0]=0;
  for(const arr of groupBest.values()){
    const next=dp.slice();
    for(let mask=0;mask<=full;mask++){
      if(dp[mask]===-Infinity)continue;
      for(let i=0;i<R;i++){
        if(mask&(1<<i))continue;
        if(arr[i]===-Infinity)continue;
        const nm=mask|(1<<i),val=dp[mask]+arr[i];
        if(val>next[nm])next[nm]=val;
      }
    }
    dp=next;
  }
  const Smax=dp[full];
  if(Smax===-Infinity)return null;
  return {Smax,L,U};
}

function spMaxFreeBox(fixedVals,L,U,SmaxTotal){
  const R=L.length,N=fixedVals.length+R,EPS=1e-9;
  const fixedSum=fixedVals.reduce((a,b)=>a+b,0),freeCap=SmaxTotal-fixedSum;
  function spOf(freeVals){
    const S=fixedSum+freeVals.reduce((a,b)=>a+b,0),A=S/N;let sp=0;
    for(const v of fixedVals)if(v>A)sp+=v-A;
    for(const v of freeVals)if(v>A)sp+=v-A;
    return sp;
  }
  let best=-Infinity;
  const total=1<<R;
  for(let mask=0;mask<total;mask++){
    const vals=new Array(R);let s=0;
    for(let i=0;i<R;i++){const v=(mask&(1<<i))?U[i]:L[i];vals[i]=v;s+=v;}
    if(s<=freeCap+EPS){const sp=spOf(vals);if(sp>best)best=sp;}
  }
  for(let flex=0;flex<R;flex++){
    const others=[];for(let i=0;i<R;i++)if(i!==flex)others.push(i);
    const M=others.length,subTotal=1<<M;
    for(let mask=0;mask<subTotal;mask++){
      const vals=new Array(R);let sumOthers=0;
      for(let mkk=0;mkk<M;mkk++){const i=others[mkk];const v=(mask&(1<<mkk))?U[i]:L[i];vals[i]=v;sumOthers+=v;}
      let v=freeCap-sumOthers;
      if(v<L[flex])v=L[flex];
      if(v>U[flex])v=U[flex];
      vals[flex]=v;
      const sp=spOf(vals);if(sp>best)best=sp;
    }
  }
  return best;
}

function h2NodeBound(k,order,cand,usedGroups,pick){
  const N=order.length,R=N-k;
  if(R<=1||R>8)return null;
  const remSlots=new Array(R);for(let i=0;i<R;i++)remSlots[i]=order[k+i];
  const asn=assignMaxSumNode(remSlots,cand,usedGroups);
  if(!asn)return null;
  const committed=new Array(k);for(let j=0;j<k;j++)committed[j]=pick[order[j]].rating;
  const fixedSum=committed.reduce((a,b)=>a+b,0);
  const SmaxTotal=fixedSum+asn.Smax;
  const spMax=spMaxFreeBox(committed,asn.L,asn.U,SmaxTotal);
  return Math.floor((SmaxTotal+spMax)/N);
}

// ---------- full brute-force oracle (verbatim from v1) ----------
function bruteBestRemaining(order,cand,usedGroups,pick,k){
  const N=order.length;
  let best=null;
  function rec(j,used,chosen){
    if(j===N){
      const full=order.map((s,idx)=> idx<k? pick[s].rating : chosen[idx-k]);
      const v=futRatingRaw(full);
      if(best===null||v>best)best=v;
      return;
    }
    const slot=order[j];
    for(const c of cand[slot]){
      if(used.has(c._group))continue;
      used.add(c._group);chosen.push(c.rating);
      rec(j+1,used,chosen);
      used.delete(c._group);chosen.pop();
    }
  }
  rec(k,new Set(usedGroups),[]);
  return best;
}

// ---------- RNG ----------
function makeRng(seed){
  let s=seed>>>0;
  return function(){ s=(s*1664525+1013904223)>>>0; return s/4294967296; };
}
function randInt(rng,lo,hi){ return lo+Math.floor(rng()*(hi-lo+1)); }

// ==========================================================================================
// A) assignMaxSumNode IN ISOLATION -- vs brute-force max-weight assignment
// ==========================================================================================
function bruteMaxAssignment(remSlots,cand,usedGroups){
  const R=remSlots.length;
  let best=-Infinity;
  function rec(i,used,sum){
    if(i===R){ if(sum>best)best=sum; return; }
    const list=cand[remSlots[i]];
    for(const c of list){
      if(usedGroups.has(c._group)||used.has(c._group))continue;
      used.add(c._group);
      rec(i+1,used,sum+c.rating);
      used.delete(c._group);
    }
  }
  rec(0,new Set(),0);
  return best===-Infinity? null : best;
}

function genAssignmentInstance(rng){
  const R=randInt(rng,2,6);
  const remSlots=[...Array(R).keys()];
  const cand=Array.from({length:R},()=>[]);
  const nSharedGroups=randInt(rng,1,3);
  const sharedGroups=[...Array(nSharedGroups).keys()].map(i=>'shared'+i);
  for(let s=0;s<R;s++){
    const list=[];
    for(const g of sharedGroups){ if(rng()<0.7) list.push({_group:g, rating:60+randInt(rng,0,39)}); }
    const nUnique=randInt(rng,0,2);
    for(let u=0;u<nUnique;u++) list.push({_group:'u'+s+'_'+u, rating:60+randInt(rng,0,39)});
    cand[s]=list;
  }
  return {R,remSlots,cand,usedGroups:new Set()};
}

function testAssignMaxSumNodeIsolated(trials,rng){
  let checked=0, mismatches=0, infeasibleAgree=0;
  for(let t=0;t<trials;t++){
    const {remSlots,cand,usedGroups}=genAssignmentInstance(rng);
    const truth=bruteMaxAssignment(remSlots,cand,usedGroups);
    const asn=assignMaxSumNode(remSlots,cand,usedGroups);
    if(truth===null){
      if(asn!==null) mismatches++; // claims feasible when it isn't -- would be a real bug
      else infeasibleAgree++;
      continue;
    }
    checked++;
    if(asn===null || Math.abs(asn.Smax-truth)>1e-9) mismatches++;
  }
  return {checked, mismatches, infeasibleAgree};
}

// ==========================================================================================
// B) spMaxFreeBox IN ISOLATION -- vs brute-force integer-grid search over the free box
// ==========================================================================================
function bruteMaxSpFreeBox(fixedVals,L,U,freeCap){
  const R=L.length,N=fixedVals.length+R,EPS=1e-9;
  const fixedSum=fixedVals.reduce((a,b)=>a+b,0);
  let best=-Infinity;
  const vals=new Array(R);
  function rec(i,sum){
    if(i===R){
      if(sum<=freeCap+EPS){
        const S=fixedSum+sum,A=S/N;let sp=0;
        for(const v of fixedVals)if(v>A)sp+=v-A;
        for(const v of vals)if(v>A)sp+=v-A;
        if(sp>best)best=sp;
      }
      return;
    }
    for(let v=L[i];v<=U[i];v++){ vals[i]=v; rec(i+1,sum+v); }
  }
  rec(0,0);
  return best;
}

function genFreeBoxInstance(rng){
  const R=randInt(rng,1,4);
  const nFixed=randInt(rng,0,3);
  const fixedVals=[];for(let i=0;i<nFixed;i++)fixedVals.push(randInt(rng,0,25));
  const L=new Array(R),U=new Array(R);
  for(let i=0;i<R;i++){
    const lo=randInt(rng,0,20);
    const width=randInt(rng,0,8); // keep grid small for brute force
    L[i]=lo;U[i]=lo+width;
  }
  const sumL=L.reduce((a,b)=>a+b,0),sumU=U.reduce((a,b)=>a+b,0);
  const freeCap = sumL + Math.floor(rng()*(sumU-sumL+1)); // somewhere inside [sumL,sumU], forces the interesting interior/vertex cases
  return {fixedVals,L,U,freeCap};
}

function testSpMaxFreeBoxIsolated(trials,rng){
  let checked=0, mismatches=0, maxGap=0, soundnessViol=0;
  for(let t=0;t<trials;t++){
    const {fixedVals,L,U,freeCap}=genFreeBoxInstance(rng);
    const truth=bruteMaxSpFreeBox(fixedVals,L,U,freeCap);
    // spMaxFreeBox takes SmaxTotal, not freeCap directly -- reconstruct: freeCap = SmaxTotal - fixedSum
    const fixedSum=fixedVals.reduce((a,b)=>a+b,0);
    const SmaxTotal=fixedSum+freeCap;
    const got=spMaxFreeBox(fixedVals,L,U,SmaxTotal);
    checked++;
    if(got < truth - 1e-9) soundnessViol++; // claiming less spread than achievable = unsound as an upper bound
    const gap=Math.abs(got-truth);
    if(gap>1e-6){ mismatches++; if(gap>maxGap)maxGap=gap; }
  }
  return {checked, mismatches, soundnessViol, maxGap};
}

// ==========================================================================================
// C) DAC's collision-fix branch, FORCED TO FIRE -- corrected targeted generator
// ==========================================================================================
// v1's genTargetedInstance built each pair with slot s1's live-scan top = group A and slot s2's
// live-scan top = group B (two DIFFERENT groups) -- so dacVec's firstHit collision map never saw
// any group with 2+ entries, and the collision-resolution loop was dead code for the entire run.
// The actual DAC bug requires two slots whose LIVE SCAN TOP PICK IS THE SAME GROUP. Fixed here.
function genTargetedInstanceForced(rng){
  const nPairs=randInt(rng,1,3);
  const N=nPairs*2+randInt(rng,0,2);
  const order=[...Array(N).keys()];
  const cand=Array.from({length:N},()=>[]);
  let nextSlot=0;
  for(let p=0;p<nPairs;p++){
    const s1=nextSlot++, s2=nextSlot++;
    const g='shared'+p; // SAME group cited by both slots -- the real collision precondition
    const r1=85+randInt(rng,0,14);   // g's rating at s1 -- independently rolled
    const r2=85+randInt(rng,0,14);   // g's rating at s2 -- independently rolled (may beat or lose to r1)
    const alt1=70+randInt(rng,0,14); // s1's own next-best (< 85, so g stays s1's live top)
    const alt2=70+randInt(rng,0,14); // s2's own next-best (< 85, so g stays s2's live top)
    cand[s1].push({_group:g, rating:r1});
    cand[s1].push({_group:'alt1_'+s1, rating:alt1});
    cand[s2].push({_group:g, rating:r2});
    cand[s2].push({_group:'alt2_'+s2, rating:alt2});
    cand[s1].sort((a,b)=>b.rating-a.rating);
    cand[s2].sort((a,b)=>b.rating-a.rating);
  }
  for(; nextSlot<N; nextSlot++){
    const s=nextSlot;
    cand[s].push({_group:'solo_'+s, rating:70+randInt(rng,0,25)});
    cand[s].push({_group:'solo2_'+s, rating:70+randInt(rng,0,25)});
    cand[s].sort((a,b)=>b.rating-a.rating);
  }
  return {N,k:0,order,cand,usedGroups:new Set(),pick:new Array(N).fill(null)};
}

function countLiveScanCollisions(N,cand,usedGroups){
  const tops=[];
  for(let s=0;s<N;s++){ for(const c of cand[s]){ if(!usedGroups.has(c._group)){ tops.push(c._group); break; } } }
  const seen=new Set(); let collided=false;
  for(const g of tops){ if(seen.has(g)){collided=true;break;} seen.add(g); }
  return collided;
}

function testDacCollisionForced(trials,rng){
  let feasible=0, forcedCollision=0, dacViol=0, r2Viol=0, h2Viol=0;
  for(let t=0;t<trials;t++){
    const inst=genTargetedInstanceForced(rng);
    const {N,k,order,cand,usedGroups,pick}=inst;
    if(countLiveScanCollisions(N,cand,usedGroups)) forcedCollision++;
    const trueMax=bruteBestRemaining(order,cand,usedGroups,pick,k);
    if(trueMax===null)continue;
    feasible++;
    const trueFloor=Math.floor(trueMax);
    const dacBound=Math.floor(futRatingRaw(dacVec(order,cand,usedGroups,pick,k)));
    const r2Bound=Math.floor(futRatingRaw(r2Vec(order,cand,usedGroups,pick,k)));
    const h2Bound=h2NodeBound(k,order,cand,usedGroups,pick);
    if(dacBound<trueFloor)dacViol++;
    if(r2Bound<trueFloor)r2Viol++;
    if(h2Bound!==null && h2Bound<trueFloor)h2Viol++;
  }
  return {feasible, forcedCollision, dacViol, r2Viol, h2Viol};
}

// ==========================================================================================
// D) COMPOSED h2NodeBound, general fuzz (kept from v1 as a final integration check)
// ==========================================================================================
function genGeneralInstance(rng){
  const N=randInt(rng,4,7);
  const kWant=randInt(rng,0,N-1);
  const order=[...Array(N).keys()];
  const nSharedGroups=randInt(rng,2,4);
  const sharedGroups=[...Array(nSharedGroups).keys()].map(i=>'shared'+i);
  const cand=[];
  for(let s=0;s<N;s++){
    const list=[];
    for(const g of sharedGroups){ if(rng()<0.6) list.push({_group:g, rating:65+randInt(rng,0,34)}); }
    const nUnique=randInt(rng,1,3);
    for(let u=0;u<nUnique;u++) list.push({_group:'u'+s+'_'+u+'_'+Math.floor(rng()*1e9), rating:65+randInt(rng,0,34)});
    list.sort((a,b)=>b.rating-a.rating);
    cand.push(list);
  }
  const usedGroups=new Set();
  const pick=new Array(N).fill(null);
  let k=0;
  for(let j=0;j<kWant;j++){
    const slot=order[j];
    let chosen=null;
    for(const c of cand[slot]){ if(!usedGroups.has(c._group)){chosen=c;break;} }
    if(!chosen)break;
    usedGroups.add(chosen._group); pick[slot]=chosen; k++;
  }
  return {N,k,order,cand,usedGroups,pick};
}

function testComposedGeneral(trials,rng){
  let checked=0, h2Viol=0, r2Viol=0;
  for(let t=0;t<trials;t++){
    const {N,k,order,cand,usedGroups,pick}=genGeneralInstance(rng);
    if(N-k<1)continue;
    const trueMax=bruteBestRemaining(order,cand,usedGroups,pick,k);
    if(trueMax===null)continue;
    checked++;
    const trueFloor=Math.floor(trueMax);
    const r2Bound=Math.floor(futRatingRaw(r2Vec(order,cand,usedGroups,pick,k)));
    const h2Bound=h2NodeBound(k,order,cand,usedGroups,pick);
    if(r2Bound<trueFloor)r2Viol++;
    if(h2Bound!==null && h2Bound<trueFloor)h2Viol++;
  }
  return {checked,h2Viol,r2Viol};
}

// ==========================================================================================
// MAIN
// ==========================================================================================
function parseArgs(){
  const args=process.argv.slice(2);
  const get=(flag,def)=>{ const i=args.indexOf(flag); return i>=0? parseInt(args[i+1],10) : def; };
  return { trials: get('--trials',20000), seed: get('--seed',12345) };
}

function main(){
  const {trials,seed}=parseArgs();

  console.log(`=== A) assignMaxSumNode isolated (${trials} trials) ===`);
  const a=testAssignMaxSumNodeIsolated(trials, makeRng(seed));
  console.log(`checked: ${a.checked}  infeasible-agreed: ${a.infeasibleAgree}  MISMATCHES vs brute-force exact max: ${a.mismatches}`);

  console.log(`\n=== B) spMaxFreeBox isolated (${trials} trials) ===`);
  const b=testSpMaxFreeBoxIsolated(trials, makeRng(seed+1));
  console.log(`checked: ${b.checked}  soundness violations (bound < true max): ${b.soundnessViol}  mismatches (any gap > 1e-6): ${b.mismatches}  max gap: ${b.maxGap.toFixed(6)}`);

  console.log(`\n=== C) DAC collision branch FORCED to fire (${trials} trials) ===`);
  const c=testDacCollisionForced(trials, makeRng(seed+2));
  console.log(`feasible: ${c.feasible}  forced-collision instances: ${c.forcedCollision}/${c.feasible}`);
  console.log(`DAC violations: ${c.dacViol} (${(100*c.dacViol/c.feasible).toFixed(2)}%)  [prior report: ~8.5%]`);
  console.log(`R2  violations: ${c.r2Viol} (expect 0)`);
  console.log(`H2  violations: ${c.h2Viol} (expect 0)`);

  console.log(`\n=== D) composed h2NodeBound, general fuzz (${trials} trials, integration check only) ===`);
  const d=testComposedGeneral(trials, makeRng(seed+3));
  console.log(`checked: ${d.checked}  R2 violations: ${d.r2Viol} (expect 0)  H2 violations: ${d.h2Viol} (expect 0)`);

  console.log(`\n=== SUMMARY ===`);
  console.log(`A/B validate the two new primitives in isolation, against oracles built for their own`);
  console.log(`preconditions, before trusting anything about their composition. C forces the actual`);
  console.log(`bug precondition instead of hoping a generic/targeted-but-wrong generator stumbles into`);
  console.log(`it. D is only meaningful once A-C are clean -- a good D number alone would NOT have`);
  console.log(`caught DAC's bug, since the original in-file fuzz (0/160) and v1's broken Test 2 both`);
  console.log(`passed while the specific precondition went untested.`);
}

main();

const MIN_SCORE_MS = 90; // very short notes won't affect scoring
const PLAYBACK_GAIN = 3.0;
// 音准分析器 V0.4.2
// 修复：V0.4.1 为了减少碎片，引入了“换音确认+合并”，但会把几个很短的音并成一个事件。
// 本版策略：
// - 只要 MIDI(最近半音)变化，就立刻进入“候选换音”流程；不再用“cents相近就当同一音”这种会吞音的逻辑。
// - 自适应确认：
//   * 如果当前事件已经持续 >= 90ms：换音需要连续确认 2 次（更抗抖）
//   * 否则：确认 1 次（更能抓到 50ms 级短音）
// - 音高计算频率提升到每 ~33ms 一次（pitchEveryNFrames=2），更容易抓短音

const UI = {
  inputProfile: document.getElementById("inputProfile"),
  keyClass: document.getElementById("keyClass"),
  aRef: document.getElementById("aRef"),
  centsTol: document.getElementById("centsTol"),
  longMs: document.getElementById("longMs"),
  wShort: document.getElementById("wShort"),

  btnStart: document.getElementById("btnStart"),
  btnStop: document.getElementById("btnStop"),

  liveNote: document.getElementById("liveNote"),
  liveHz: document.getElementById("liveHz"),
  liveCents: document.getElementById("liveCents"),
  liveClass: document.getElementById("liveClass"),

  countAll: document.getElementById("countAll"),
  countLong: document.getElementById("countLong"),
  countShortIn: document.getElementById("countShortIn"),
  countOther: document.getElementById("countOther"),

  viewFilter: document.getElementById("viewFilter"),

  btnPlayAll: document.getElementById("btnPlayAll"),
  btnPlaySel: document.getElementById("btnPlaySel"),
  btnRefSel: document.getElementById("btnRefSel"),
  btnStopAudio: document.getElementById("btnStopAudio"),
  selectHint: document.getElementById("selectHint"),

  kpiOverall: document.getElementById("kpiOverall"),
  kpiOverallSub: document.getElementById("kpiOverallSub"),
  kpiLong: document.getElementById("kpiLong"),
  kpiLongSub: document.getElementById("kpiLongSub"),
  kpiShort: document.getElementById("kpiShort"),
  kpiShortSub: document.getElementById("kpiShortSub"),

  eventsTbody: document.querySelector("#eventsTable tbody"),
  reportMeta: document.getElementById("reportMeta"),

  meterFill: document.getElementById("meterFill"),
  meterText: document.getElementById("meterText"),
  scope: document.getElementById("scope"),
  btnTolMinus: document.getElementById("btnTolMinus"),
  btnTolPlus: document.getElementById("btnTolPlus"),
  centsTolVal: document.getElementById("centsTolVal"),
  btnFilterAll: document.getElementById("btnFilterAll"),
  btnFilterLong: document.getElementById("btnFilterLong"),
  btnFilterShort: document.getElementById("btnFilterShort"),
  btnFilterOther: document.getElementById("btnFilterOther"),
  trend: document.getElementById("trend"),
  trendMeta: document.getElementById("trendMeta"),
  btnExportVideo: document.getElementById("btnExportVideo"),
  exportProg: document.getElementById("exportProg"),
  exportProgTitle: document.getElementById("exportProgTitle"),
  exportProgPct: document.getElementById("exportProgPct"),
  exportBarFill: document.getElementById("exportBarFill"),
  exportProgHint: document.getElementById("exportProgHint"),
  scoreLong: document.getElementById("scoreLong"),
  scoreShort: document.getElementById("scoreShort"),
  scoreLongSub: document.getElementById("scoreLongSub"),
  scoreShortSub: document.getElementById("scoreShortSub"),
  scoreLongBadge: document.getElementById("scoreLongBadge"),
  scoreShortBadge: document.getElementById("scoreShortBadge"),
};

const CFG = {
  hopMs: 10,
  minEventMs: 30,
  pitchEveryNFrames: 2,      // ~33ms (提升对短音的捕捉)
  mergeGapMs: 40,            // 合并更保守（只合并非常短的断裂）
  longEventSwitchMs: 90,     // 当前事件≥该值时，换音确认更严格
  confirmShort: 1,
  confirmLong: 2,
  playbackFadeMs: 12,
};

let audioCtx=null, analyser=null, micStream=null, rafId=null;
let isRunning=false, startPerf=0;
let buf=null, sampleRate=48000;

let events=[], curEvent=null;
let pitchTimeline=[]; // {tMs, cents, pass, category, note, midi}
let frameCount=0, lastPitch=null;

// debounced switch state
let pendingMidi=null, pendingCount=0;

let procNode=null, recordedChunks=[], recordedSamples=0, recordedBuffer=null;

let playCtx=null, currentNode=null;
let selectedIndex=-1;

// ---------------- utils ----------------
function nowMs(){ return performance.now() - startPerf; }

const NOTE_NAMES=["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];
function freqToMidi(f){ return 69 + 12*Math.log2(f/440); }
function midiToFreqEqual(m,a4){ return a4*Math.pow(2,(m-69)/12); }
function midiToName(midi){
  const m=Math.round(midi);
  const name=NOTE_NAMES[(m+1200)%12];
  const octave=Math.floor(m/12)-1;
  return {name,octave,midiRounded:m};
}
function centsOff(fMeas,fTarget){ return 1200*Math.log2(fMeas/fTarget); }
function stripOctave(label){ return label.replace(/-?\d+$/,""); }
function median(arr){
  if(!arr.length) return NaN;
  const a=[...arr].sort((x,y)=>x-y);
  const mid=Math.floor(a.length/2);
  return a.length%2?a[mid]:(a[mid-1]+a[mid])/2;
}
function mean(arr){
  if(!arr.length) return NaN;
  let s=0; for(const v of arr) s+=v;
  return s/arr.length;
}
function meanAbsCents(list){
  if(!list.length) return NaN;
  let s=0; for(const e of list) s+=Math.abs(e.cents);
  return s/list.length;
}

function clamp(v,min,max){ return Math.max(min, Math.min(max, v)); }

// 评分规则：
// 1) 基础分 = 绿色(合格)比例 * 100（只统计 pass/fail；other 默认不计入短音评分）
// 2) 连续绿色：每连续 1 个额外 +0.8 分（从第2个开始），最多 +12
// 3) 连续红色≥3：从第3个开始每个 -1.0 分，最多 -12
// 4) 最终分 clamp 到 0..100；≥50 为及格
function computeCategoryScore(category){
  const list = events.filter(e=>e.category===category);
  const n = list.length;
  if(n===0){
    return {score:50, green:0, red:0, streakG:0, streakR:0, bonus:0, penalty:0, ratio:0, n:0};
  }

  let green=0, red=0;
  for(const e of list){
    if(e.pass) green++; else red++;
  }
  const denom = green + red;
  const ratio = denom>0 ? (green/denom) : 0;
  const base = ratio * 100;

  // streaks at end
  let streakG=0, streakR=0;
  for(let i=list.length-1;i>=0;i--){
    if(list[i].pass){ streakG++; }
    else break;
  }
  for(let i=list.length-1;i>=0;i--){
    if(!list[i].pass){ streakR++; }
    else break;
  }

  const bonus = clamp((streakG<=1?0:(streakG-1)*0.8), 0, 12);
  const penalty = clamp((streakR<3?0:(streakR-2)*1.0), 0, 12);

  const score = clamp(base + bonus - penalty, 0, 100);
  return {score, green, red, streakG, streakR, bonus, penalty, ratio, n};
}

function renderLiveScores(){
  if(!UI.scoreLong || !UI.scoreShort) return;

  const L = computeCategoryScore("long");
  const S = computeCategoryScore("short_in");

  UI.scoreLong.textContent = String(Math.round(L.score));
  UI.scoreShort.textContent = String(Math.round(S.score));

  UI.scoreLongSub.textContent =
    L.n===0 ? "等待事件…" :
    `绿${L.green}/红${L.red} · 绿率 ${(L.ratio*100).toFixed(0)}% · 连绿${L.streakG} +${L.bonus.toFixed(1)} · 连红${L.streakR} -${L.penalty.toFixed(1)}`;

  UI.scoreShortSub.textContent =
    S.n===0 ? "等待事件…" :
    `绿${S.green}/红${S.red} · 绿率 ${(S.ratio*100).toFixed(0)}% · 连绿${S.streakG} +${S.bonus.toFixed(1)} · 连红${S.streakR} -${S.penalty.toFixed(1)}`;

  // badges
  const passL = L.score >= 50;
  const passS = S.score >= 50;

  UI.scoreLongBadge.textContent = passL ? "及格 ✅（≥50）" : "不及格 ❌（<50）";
  UI.scoreShortBadge.textContent = passS ? "及格 ✅（≥50）" : "不及格 ❌（<50）";

  UI.scoreLongBadge.classList.toggle("pass", passL);
  UI.scoreLongBadge.classList.toggle("fail", !passL);
  UI.scoreShortBadge.classList.toggle("pass", passS);
  UI.scoreShortBadge.classList.toggle("fail", !passS);
}


// ---------------- key classification (major) ----------------
const MAJOR_SCALE = {
  "C":["C","D","E","F","G","A","B"],
  "G":["G","A","B","C","D","E","F#"],
  "D":["D","E","F#","G","A","B","C#"],
  "A":["A","B","C#","D","E","F#","G#"],
  "E":["E","F#","G#","A","B","C#","D#"],
  "B":["B","C#","D#","E","F#","G#","A#"],
  "F":["F","G","A","Bb","C","D","E"],
  "Bb":["Bb","C","D","Eb","F","G","A"],
  "Eb":["Eb","F","G","Ab","Bb","C","D"],
  "Ab":["Ab","Bb","C","Db","Eb","F","G"],
};
function normalizePC(pc){
  const map={"Bb":"A#","Eb":"D#","Ab":"G#","Db":"C#","Gb":"F#","Cb":"B","Fb":"E","E#":"F","B#":"C"};
  return map[pc]||pc;
}
function isInKey(pitchClass,key){
  const scale=MAJOR_SCALE[key]||MAJOR_SCALE["D"];
  const set=new Set(scale.map(normalizePC));
  return set.has(normalizePC(pitchClass));
}

// ---------------- profile & YIN ----------------
function getProfile(){
  if(UI.inputProfile.value==="oboe"){
    return {label:"OBOE", fftSize:4096, rmsMin:0.004, confMin:0.55, fMinHz:110, fMaxHz:1400, yinThreshold:0.12};
  }
  return {label:"VOICE", fftSize:8192, rmsMin:0.002, confMin:0.30, fMinHz:50, fMaxHz:1200, yinThreshold:0.18};
}

function yinPitch(buffer,sr,fMin,fMax,thr){
  const N=buffer.length;
  const maxTau=Math.min(Math.floor(sr/fMin), Math.floor(N/2));
  const minTau=Math.max(2, Math.floor(sr/fMax));

  const d=new Float32Array(maxTau+1);
  for(let tau=minTau;tau<=maxTau;tau++){
    let sum=0;
    for(let i=0;i<N-tau;i++){
      const diff=buffer[i]-buffer[i+tau];
      sum += diff*diff;
    }
    d[tau]=sum;
  }

  const cmnd=new Float32Array(maxTau+1);
  cmnd[0]=1;
  let running=0;
  for(let tau=1;tau<=maxTau;tau++){
    running += d[tau];
    cmnd[tau] = running ? (d[tau]*tau)/running : 1;
  }

  let tauEst=-1;
  for(let tau=minTau;tau<=maxTau;tau++){
    if(cmnd[tau] < thr){
      while(tau+1<=maxTau && cmnd[tau+1] < cmnd[tau]) tau++;
      tauEst=tau;
      break;
    }
  }
  if(tauEst===-1) return null;

  const tau=tauEst;
  const x0=tau>1?tau-1:tau;
  const x2=tau+1<=maxTau?tau+1:tau;
  const s0=cmnd[x0], s1=cmnd[tau], s2=cmnd[x2];
  let betterTau=tau;
  const denom=(2*s1 - s2 - s0);
  if(denom!==0) betterTau = tau + (s2 - s0)/(2*denom);

  const freq = sr / betterTau;
  const conf = Math.max(0, Math.min(1, 1 - cmnd[tauEst]));
  if(!isFinite(freq) || freq<=0) return null;
  return {freqHz:freq, confidence:conf};
}

// ---------------- meter & scope ----------------
function drawScopeAndMeter(timeBuf,profile,pitch){
  let rms=0;
  for(let i=0;i<timeBuf.length;i++) rms += timeBuf[i]*timeBuf[i];
  rms=Math.sqrt(rms/timeBuf.length);

  const db=20*Math.log10(rms+1e-9);
  const pct=Math.max(0,Math.min(100,(db+60)/60*100));
  UI.meterFill.style.width=`${pct.toFixed(1)}%`;
  UI.meterText.textContent=isFinite(db)?`${db.toFixed(1)} dBFS`:"— dBFS";

  const c=UI.scope;
  if(!c) return;
  const ctx=c.getContext("2d");
  const w=c.width, h=c.height;
  ctx.clearRect(0,0,w,h);

  ctx.globalAlpha=0.35;
  ctx.beginPath(); ctx.moveTo(0,h/2); ctx.lineTo(w,h/2);
  ctx.strokeStyle="#6aa8ff"; ctx.stroke();
  ctx.globalAlpha=1;

  ctx.beginPath();
  const step=Math.max(1,Math.floor(timeBuf.length/w));
  for(let x=0;x<w;x++){
    const i=x*step;
    const y=(0.5-timeBuf[i]/2)*h;
    if(x===0) ctx.moveTo(x,y); else ctx.lineTo(x,y);
  }
  ctx.strokeStyle="#eaeef7"; ctx.stroke();

  ctx.font="12px ui-sans-serif, system-ui";
  ctx.fillStyle="#9aa3b2";
  const p=pitch?`${pitch.freqHz.toFixed(1)}Hz · conf ${pitch.confidence.toFixed(2)}`:"—";
  ctx.fillText(`${profile.label} · ${p}`,10,18);
}

// ---------------- recorder ----------------
function setupRecorder(src){
  recordedChunks=[]; recordedSamples=0; recordedBuffer=null;
  const bufferSize=4096;
  procNode=audioCtx.createScriptProcessor(bufferSize,1,1);
  src.connect(procNode);

  // Safari: must connect to destination (silent) to keep processing
  const zero=audioCtx.createGain();
  zero.gain.value=0;
  procNode.connect(zero);
  zero.connect(audioCtx.destination);

  procNode.onaudioprocess=(e)=>{
    if(!isRunning) return;
    const input=e.inputBuffer.getChannelData(0);
    const copy=new Float32Array(input.length);
    copy.set(input);
    recordedChunks.push(copy);
    recordedSamples += copy.length;
  };
}

function buildRecordedBuffer(){
  if(!recordedSamples || !recordedChunks.length) return null;
  const data=new Float32Array(recordedSamples);
  let off=0;
  for(const ch of recordedChunks){
    data.set(ch,off);
    off += ch.length;
  }
  recordedChunks=[];
  const b=audioCtx.createBuffer(1,data.length,sampleRate);
  b.getChannelData(0).set(data);
  return b;
}

// ---------------- events ----------------
function newEvent(tMs, detectedLabel, targetLabel, midiRounded, fTarget, inKey){
  return {
    startMs:tMs, lastMs:tMs,
    detectedLabel, targetLabel, midiRounded, fTarget, inKey,
    hzArr:[], centsArr:[], confArr:[],
  };
}

function finalizeEvent(ev, params){
  const dur=ev.lastMs-ev.startMs;
  if(dur < CFG.minEventMs) return null;

  const isLong = dur >= params.longMs;
  let category = isLong ? "long" : "short_in";
  if(!isLong && !ev.inKey) category="other";

  let sIdx=0, eIdx=ev.centsArr.length;
  if(isLong && ev.centsArr.length>10){
    const trimMs=Math.min(60, dur*0.2);
    const trimFrames=Math.floor(trimMs/CFG.hopMs);
    sIdx=Math.min(trimFrames, ev.centsArr.length-1);
    eIdx=Math.max(sIdx+1, ev.centsArr.length-trimFrames);
  }

  const centsMed=median(ev.centsArr.slice(sIdx,eIdx));
  const hzMed=median(ev.hzArr.slice(sIdx,eIdx));
  const confMean=mean(ev.confArr.slice(sIdx,eIdx));
  const pass=Math.abs(centsMed) <= params.centsTol;

  return {
    startMs:Math.round(ev.startMs),
    endMs:Math.round(ev.lastMs),
    durMs:Math.round(dur),
    detectedLabel:ev.detectedLabel,
    targetLabel:ev.targetLabel,
    midiRounded:ev.midiRounded,
    hzMeas:hzMed,
    hzTarget:ev.fTarget,
    cents:centsMed,
    confidence:confMean,
    category,
    pass,
  };
}

function maybeMergeWithPrev(fin){
  if(!fin || !events.length) return false;
  const prev=events[events.length-1];
  const gap = fin.startMs - prev.endMs;
  // 只在非常短的“断裂”情况下合并，且必须同目标音
  if(gap <= CFG.mergeGapMs && prev.midiRounded === fin.midiRounded){
    const d1=Math.max(1, prev.durMs);
    const d2=Math.max(1, fin.durMs);
    prev.endMs = fin.endMs;
    prev.durMs = prev.endMs - prev.startMs;
    prev.hzMeas = (prev.hzMeas*d1 + fin.hzMeas*d2)/(d1+d2);
    prev.cents = (prev.cents*d1 + fin.cents*d2)/(d1+d2);
    prev.pass = Math.abs(prev.cents) <= Number(UI.centsTol.value);

    const longMs=Number(UI.longMs.value);
    const isLong = prev.durMs >= longMs;
    if(isLong) prev.category="long";
    return true;
  }
  return false;
}

function handleNoPitch(tMs, params){
  if(!curEvent) return;
  const gap=tMs - curEvent.lastMs;
  if(gap >= 70){
    const fin=finalizeEvent(curEvent,params);
    if(fin){
      if(!maybeMergeWithPrev(fin)) events.push(fin);
    }
    curEvent=null;
    pendingMidi=null; pendingCount=0;
    updateCounters(params);
  }
}

// ---------------- playback ----------------
function ensurePlayCtx(){
  if(!playCtx) playCtx = new (window.AudioContext || window.webkitAudioContext)();
  if(playCtx.state==="suspended") playCtx.resume();
  return playCtx;
}
function stopAudio(){
  try{ if(currentNode) currentNode.await stop(); }catch(e){}
  currentNode=null;
  UI.btnStopAudio.disabled=true;
}
function playAll(){
  if(!recordedBuffer) return;
  const ctx=ensurePlayCtx();
  stopAudio();

  const src=ctx.createBufferSource();
  src.buffer=recordedBuffer;

  const g=ctx.createGain();
  g.gain.value=0.0001;
  src.connect(g); g.connect(ctx.destination);

  const now=ctx.currentTime;
  g.gain.exponentialRampToValueAtTime(1.0, now+0.03);
  src.start(now);

  currentNode=src;
  UI.btnStopAudio.disabled=false;
  src.onended=()=>{ UI.btnStopAudio.disabled=true; currentNode=null; };
}
function playSegment(e){
  if(!recordedBuffer) return;
  const ctx=ensurePlayCtx();
  stopAudio();

  const src=ctx.createBufferSource();
  src.buffer=recordedBuffer;

  const g=ctx.createGain();
  g.gain.value=0.0001;
  src.connect(g); g.connect(ctx.destination);

  const startSec=e.startMs/1000;
  const durSec=Math.max(0.02,(e.endMs-e.startMs)/1000);
  const now=ctx.currentTime;
  const fade=CFG.playbackFadeMs/1000;

  g.gain.setValueAtTime(0.0001, now);
  g.gain.exponentialRampToValueAtTime(1.0, now+fade);
  g.gain.setValueAtTime(1.0, now+Math.max(fade, durSec-fade));
  g.gain.exponentialRampToValueAtTime(0.0001, now+durSec);

  src.start(now, startSec, durSec);
  src.stop(now+durSec+0.02);

  currentNode=src;
  UI.btnStopAudio.disabled=false;
  src.onended=()=>{ UI.btnStopAudio.disabled=true; currentNode=null; };
}
function playReferenceTone(freq){
  const ctx=ensurePlayCtx();
  stopAudio();

  const osc=ctx.createOscillator();
  const g=ctx.createGain();
  osc.type="sine";
  osc.frequency.value=freq;
  g.gain.value=0.0001;
  osc.connect(g); g.connect(ctx.destination);

  const now=ctx.currentTime;
  const dur=2.0;
  const fade=0.03;
  g.gain.setValueAtTime(0.0001, now);
  g.gain.exponentialRampToValueAtTime(0.6, now+fade);
  g.gain.setValueAtTime(0.6, now+dur-fade);
  g.gain.exponentialRampToValueAtTime(0.0001, now+dur);

  osc.start(now);
  osc.stop(now+dur+0.02);

  currentNode=osc;
  UI.btnStopAudio.disabled=false;
  osc.onended=()=>{ UI.btnStopAudio.disabled=true; currentNode=null; };
}

// ---------------- UI helpers ----------------
function readParams(){
  return {
    keyClass: UI.keyClass.value,
    aRef: Number(UI.aRef.value),
    centsTol: Number(UI.centsTol.value),
    longMs: 150,
    wShort: 0.40,
  };
}

function renderLive(info){
  if(!info){
    UI.liveNote.textContent="—";
    UI.liveHz.textContent="—";
    UI.liveCents.textContent="—";
    return;
  }
  UI.liveNote.textContent=info.detectedLabel;
  UI.liveHz.textContent=`${info.hz.toFixed(1)} Hz`;
  UI.liveCents.textContent=`${info.cents>=0?"+":""}${info.cents.toFixed(1)} c`;
}

function updateCounters(params){
  let lc=0, sc=0, oc=0;
  for(const e of events){
    if(e.category==="long") lc++;
    else if(e.category==="short_in") sc++;
    else oc++;
  }
  UI.countAll.textContent=String(events.length);
  UI.countLong.textContent=String(lc);
  UI.countShortIn.textContent=String(sc);
  UI.countOther.textContent=String(oc);

  renderLiveScores();

  if(UI.kpiOverallSub) UI.kpiOverallSub.textContent =
    `分类调性=${params.keyClass}大调 · A4=${params.aRef}Hz · 阈值±${params.centsTol}c · 长音≥${params.longMs}ms · (V0.4.2 防吞音)`;
}

function computeKpis(params){
  const evs = (events||[]).map(e=>{
    if(e && typeof e.durMs==='number' && e.durMs < MIN_SCORE_MS){
      return {...e, category:'other', inKey:false};
    }
    return e;
  });

  // Base pass ratios
  const longs = evs.filter(e=>e.category==="long");
  const shorts = evs.filter(e=>e.category==="short_in");
  const other = evs.filter(e=>e.category==="other");

  const longTotal = longs.length;
  const shortTotal = shorts.length;
  const otherTotal = other.length;

  const longPass = longs.filter(e=>e.pass).length;
  const shortPass = shorts.filter(e=>e.pass).length;

  // Convert to 0..100 score (not percent string)
  const longScore = longTotal ? (longPass/longTotal)*100 : 0;
  const shortScore = shortTotal ? (shortPass/shortTotal)*100 : 0;

  // Short-category participation rule:
  // If short_in count <= 20% of total notes, exclude short from overall.
  const totalNotes = longTotal + shortTotal + otherTotal;
  const shortShare = totalNotes ? (shortTotal/totalNotes) : 0;

  let overallScore = longScore;
  let overallMode = "only_long";
  if(shortShare > 0.20){
    // Use fixed weight (0.40) for short category, professional & stable
    const wL = 1.0;
    const wS = 0.40;
    overallScore = (wL*longScore + wS*shortScore) / (wL + wS);
    overallMode = "long_plus_short";
  }

  return {
    overallScore,
    overallMode,
    shortShare,
    totalNotes,
    longTotal,longPass,longScore,
    shortTotal,shortPass,shortScore,
    otherTotal,
    longAbs:meanAbsCents(longs),
    shortAbs:meanAbsCents(shorts),
    allAbs:meanAbsCents(longs.concat(shorts)),
  };
}

function renderReport(params){
  const k=computeKpis(params);

  UI.kpiOverall.textContent = `${Math.round(k.overallScore)}`;
  if(UI.kpiLong) UI.kpiLong.textContent = k.longTotal ? `${Math.round(k.longScore)}` : "—";
  if(UI.kpiShort) UI.kpiShort.textContent = k.shortTotal ? `${Math.round(k.shortScore)}` : "—";

  if(UI.kpiLongSub) UI.kpiLongSub.textContent=k.longTotal?`${k.longPass}/${k.longTotal} · 平均|cents|=${k.longAbs.toFixed(1)}`:"无长音事件";
  if(UI.kpiShortSub) UI.kpiShortSub.textContent=k.shortTotal?`${k.shortPass}/${k.shortTotal} · 平均|cents|=${k.shortAbs.toFixed(1)}`:"无短音-调内事件";
  if(UI.kpiOverallSub) UI.kpiOverallSub.textContent = `综合分(满分100)：${k.overallMode==="only_long"?"仅按长音（短音≤20%不计入）":"长音+短音-调内(0.40权重)"} · 其他=${k.otherTotal} · 平均|cents|=${k.allAbs.toFixed(1)} · 阈值±${params.centsTol}c`;

  UI.reportMeta.textContent = `本次设置：输入=${UI.inputProfile.value==="voice"?"人声":"双簧管"} · 分类调性=${params.keyClass}大调 · A4=${params.aRef}Hz · 阈值±${params.centsTol}c · 长音阈值=150ms(固定) · 短音权重=0.40(固定) · 事件数=${events.length} · 回放=${recordedBuffer?"可用":"不可用"}`;

  renderTable();
  UI.btnPlayAll.disabled = !recordedBuffer;
  UI.btnStopAudio.disabled = true;
  setSelectedIndex(-1);
}

function setSelectedIndex(i){
  selectedIndex=i;
  const has=i>=0 && i<events.length;
  UI.btnPlaySel.disabled = !(has && recordedBuffer);
  UI.btnRefSel.disabled = !has;
  if(!has){
    UI.selectHint.textContent="未选中事件：点击表格任意一行即可选中并回放。";
  } else {
    const e=events[i];
    UI.selectHint.textContent=`已选中：#${i+1} ${e.targetLabel} · ${e.startMs}-${e.endMs}ms · ${e.category}`;
  }
}

function renderTable(){
  const f=UI.viewFilter.value;
  const rows=[];
  for(let i=0;i<events.length;i++){
    const e=events[i];
    if(f==="all" ||
      (f==="long" && e.category==="long") ||
      (f==="short_in" && e.category==="short_in") ||
      (f==="other" && e.category==="other")){
      rows.push({e, idx:i});
    }
  }

  UI.eventsTbody.innerHTML="";
  rows.forEach((r,disp)=>{
    const e=r.e;
    const tr=document.createElement("tr");
    tr.dataset.index=String(r.idx);
    if(r.idx===selectedIndex) tr.classList.add("selected");

    const passCls=e.pass?"good":"bad";
    const passText=e.pass?"✅":"❌";
    let cat="";
    if(e.category==="long") cat=`<span class="badge in">Long</span>`;
    else if(e.category==="short_in") cat=`<span class="badge in">Short·调内</span>`;
    else cat=`<span class="badge other">Other</span>`;

    tr.innerHTML = `
      <td>${disp+1}</td>
      <td>${e.startMs}–${e.endMs}</td>
      <td>${e.durMs}</td>
      <td>${e.detectedLabel}</td>
      <td>${e.targetLabel}</td>
      <td>${e.hzMeas.toFixed(1)}</td>
      <td>${e.hzTarget.toFixed(1)}</td>
      <td class="${passCls}">${e.cents>=0?"+":""}${e.cents.toFixed(1)}</td>
      <td class="${passCls}">${passText}</td>
      <td>${cat}</td>
    `;
    UI.eventsTbody.appendChild(tr);
  });
}

// row selection
UI.eventsTbody.addEventListener("click",(ev)=>{
  const tr=ev.target.closest("tr");
  if(!tr) return;
  setSelectedIndex(Number(tr.dataset.index));
  renderTable();
});

// filter
UI.viewFilter.addEventListener("change", ()=>{
  renderTable();

function setFilter(val){
  UI.viewFilter.value = val;
  // update button states
  const btns=[UI.btnFilterAll,UI.btnFilterLong,UI.btnFilterShort,UI.btnFilterOther].filter(Boolean);
  for(const b of btns){
    b.classList.toggle("active", b.dataset.filter===val);
  }
  renderTable();
  setSelectedIndex(-1);
  if(typeof renderTrend==='function'){ try{ renderTrend(); }catch(e){} }
}
if(UI.btnFilterAll){
  UI.btnFilterAll.addEventListener("click", ()=>setFilter("all"));
  UI.btnFilterLong.addEventListener("click", ()=>setFilter("long"));
  UI.btnFilterShort.addEventListener("click", ()=>setFilter("short_in"));
  UI.btnFilterOther.addEventListener("click", ()=>setFilter("other"));
}
  setSelectedIndex(-1);
});



function getFilteredEvents(){
  const f = UI.viewFilter.value;
  if(f==="all") return events;
  return events.filter(e=>e.category===f);
}

function getFilteredTimeline(){
  const f = UI.viewFilter.value;
  if(f==="all") return pitchTimeline;
  return pitchTimeline.filter(p=>p.category===f);
}

function stddev(arr){
  if(!arr.length) return NaN;
  const m = arr.reduce((s,v)=>s+v,0)/arr.length;
  const v = arr.reduce((s,x)=>s+(x-m)*(x-m),0)/arr.length;
  return Math.sqrt(v);
}

function renderTrend(){
  if(!UI.trend) return;
  const c = UI.trend;
  const ctx = c.getContext("2d");
  const w=c.width, h=c.height;
  ctx.clearRect(0,0,w,h);

  // background + grid
  ctx.fillStyle="#0b0c10";
  ctx.fillRect(0,0,w,h);

  ctx.globalAlpha=0.35;
  ctx.strokeStyle="#232838";
  for(const y of [h*0.2,h*0.4,h*0.6,h*0.8]){
    ctx.beginPath(); ctx.moveTo(0,y); ctx.lineTo(w,y); ctx.stroke();
  }
  for(const x of [w*0.2,w*0.4,w*0.6,w*0.8]){
    ctx.beginPath(); ctx.moveTo(x,0); ctx.lineTo(x,h); ctx.stroke();
  }
  ctx.globalAlpha=1;

  const tl = getFilteredTimeline();
  if(!tl.length){
    if(UI.trendMeta) UI.trendMeta.textContent="—（无数据）";
    ctx.fillStyle="#9aa3b2";
    ctx.font="14px ui-sans-serif, system-ui";
    ctx.fillText("无数据：请先录制并结束生成报告", 18, 28);
    return;
  }

  const t0 = tl[0].tMs;
  const t1 = tl[tl.length-1].tMs;
  const dt = Math.max(1, t1-t0);

  const centsTol = Number(UI.centsTol.value);
  const yCenter = h/2;

  // draw tolerance band
  ctx.globalAlpha=0.18;
  ctx.fillStyle="#6aa8ff";
  const yTol = (centsTol/50) * (h*0.4); // map 50c -> 40% height
  ctx.fillRect(0, yCenter-yTol, w, yTol*2);
  ctx.globalAlpha=1;

  // plot samples
  const mapY = (cents)=>{
    const scale = (h*0.4)/50; // 50 cents -> 40% height
    return yCenter - cents*scale;
  };

  ctx.lineWidth=2;
  let prev=null;
  for(const p of tl){
    const x = ((p.tMs - t0)/dt)*w;
    const y = mapY(p.cents);
    // line
    if(prev){
      ctx.strokeStyle = "#eaeef7";
      ctx.globalAlpha=0.25;
      ctx.beginPath(); ctx.moveTo(prev.x, prev.y); ctx.lineTo(x,y); ctx.stroke();
      ctx.globalAlpha=1;
    }
    // point
    ctx.fillStyle = p.pass ? "#4ad27a" : "#ff5a6a";
    ctx.beginPath(); ctx.arc(x,y,2.4,0,Math.PI*2); ctx.fill();
    prev={x,y};
  }

  // axis labels
  ctx.fillStyle="#9aa3b2";
  ctx.font="12px ui-sans-serif, system-ui";
  ctx.fillText(`0c`, 8, yCenter-6);
  ctx.fillText(`+${centsTol}c`, 8, yCenter - yTol - 6);
  ctx.fillText(`-${centsTol}c`, 8, yCenter + yTol + 14);

  // stats
  const centsArr = tl.map(p=>p.cents);
  const sd = stddev(centsArr);
  const absMean = centsArr.reduce((s,v)=>s+Math.abs(v),0)/centsArr.length;

  if(UI.trendMeta){
    const f = UI.viewFilter.value;
    const name = f==="all"?"全部":(f==="long"?"长音":(f==="short_in"?"短音-调内":"其他"));
    UI.trendMeta.textContent = `${name} · 样本${tl.length} · 平均|cents|=${absMean.toFixed(1)} · 波动SD=${sd.toFixed(1)}（越大越不稳）`;
  }
}

// playback controls
UI.btnPlayAll.addEventListener("click", ()=>playAll());
UI.btnPlaySel.addEventListener("click", ()=>{
  if(selectedIndex>=0) playSegment(events[selectedIndex]);
});
UI.btnRefSel.addEventListener("click", ()=>{
  if(selectedIndex>=0) playReferenceTone(events[selectedIndex].hzTarget);
});
UI.btnStopAudio.addEventListener("click", ()=>stopAudio());

// ---------------- main ----------------
async function start(){
  if(isRunning) return;

  events=[]; curEvent=null;
  pitchTimeline=[];
  frameCount=0; lastPitch=null;
  pendingMidi=null; pendingCount=0;

  recordedBuffer=null;
  UI.eventsTbody.innerHTML="";
  UI.reportMeta.textContent="";
  UI.kpiOverall.textContent="—";
  if(UI.kpiLong) UI.kpiLong.textContent="—";
  if(UI.kpiShort) UI.kpiShort.textContent="—";
  setSelectedIndex(-1);
  UI.btnPlayAll.disabled=true;
  UI.btnStopAudio.disabled=true;

  audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  sampleRate = audioCtx.sampleRate;
  if(audioCtx.state==="suspended") await audioCtx.resume();

  micStream = await navigator.mediaDevices.getUserMedia({
    audio:{echoCancellation:false,noiseSuppression:false,autoGainControl:false}
  });

  const src=audioCtx.createMediaStreamSource(micStream);

  const profile=getProfile();
  analyser=audioCtx.createAnalyser();
  analyser.fftSize=profile.fftSize;
  analyser.smoothingTimeConstant=0;
  src.connect(analyser);

  buf=new Float32Array(analyser.fftSize);

  setupRecorder(src);

  isRunning=true;
  UI.btnStart.disabled=true;
  UI.btnStop.disabled=false;
  UI.liveClass.textContent="录制中…";
  startPerf=performance.now();

  const loop=()=>{
    if(!isRunning) return;

    analyser.getFloatTimeDomainData(buf);
    let currentRms=0;
    for(let i=0;i<buf.length;i++) currentRms += buf[i]*buf[i];
    currentRms = Math.sqrt(currentRms/buf.length);
    const params=readParams();
    const prof=getProfile();

    if(analyser.fftSize !== prof.fftSize){
      analyser.fftSize = prof.fftSize;
      buf = new Float32Array(analyser.fftSize);
      analyser.getFloatTimeDomainData(buf);
    let currentRms=0;
    for(let i=0;i<buf.length;i++) currentRms += buf[i]*buf[i];
    currentRms = Math.sqrt(currentRms/buf.length);
    }

    frameCount++;
    if(frameCount % CFG.pitchEveryNFrames === 0){
      // RMS gate
      let rms=0;
      for(let i=0;i<buf.length;i++) rms += buf[i]*buf[i];
      rms=Math.sqrt(rms/buf.length);

      if(rms >= prof.rmsMin){
        const yin = yinPitch(buf, sampleRate, prof.fMinHz, prof.fMaxHz, prof.yinThreshold);
        lastPitch = (yin && yin.confidence>=0.05) ? yin : null;
      } else {
        lastPitch = null;
      }
    }

    const tMs=nowMs();
    drawScopeAndMeter(buf, prof, lastPitch);

    if(!lastPitch || lastPitch.confidence < prof.confMin){
      handleNoPitch(tMs, params);
      renderLive(null);
      rafId=requestAnimationFrame(loop);
      return;
    }

    const f=lastPitch.freqHz;
    const midi=freqToMidi(f);
    const nm=midiToName(midi);
    const midiRounded=nm.midiRounded;

    const detectedLabel=`${nm.name}${nm.octave}`;
    const fTarget=midiToFreqEqual(midiRounded, params.aRef);
    const tgt=midiToName(midiRounded);
    const targetLabel=`${tgt.name}${tgt.octave}`;
    const cents=centsOff(f,fTarget);

    const pc=stripOctave(targetLabel);
    const inKey=isInKey(pc, params.keyClass);

    if(!curEvent){
      curEvent=newEvent(tMs, detectedLabel, targetLabel, midiRounded, fTarget, inKey);
      pendingMidi=null; pendingCount=0;
    } else {
      const sameMidi = (curEvent.midiRounded === midiRounded);

      if(sameMidi){
        pendingMidi=null; pendingCount=0;
        // stay in event
        curEvent.detectedLabel = detectedLabel;
        curEvent.inKey = inKey;
        curEvent.fTarget = fTarget;
      } else {
        // candidate switch: self-adaptive confirm
        const curDur = tMs - curEvent.startMs;
        const need = (curDur >= CFG.longEventSwitchMs) ? CFG.confirmLong : CFG.confirmShort;

        if(pendingMidi !== midiRounded){
          pendingMidi = midiRounded;
          pendingCount = 1;
        } else {
          pendingCount++;
        }

        if(pendingCount >= need){
          const fin=finalizeEvent(curEvent, params);
          if(fin){
            if(!maybeMergeWithPrev(fin)) events.push(fin);
          }
          curEvent=newEvent(tMs, detectedLabel, targetLabel, midiRounded, fTarget, inKey);
          pendingMidi=null; pendingCount=0;
        }
      }
    }

    // record samples into current event (whether switched or not)
    curEvent.lastMs = tMs;
    curEvent.hzArr.push(f);
    curEvent.centsArr.push(cents);
    curEvent.confArr.push(lastPitch.confidence);

    // timeline sample for trend/video
    pitchTimeline.push({tMs: tMs, cents: cents, pass: Math.abs(cents) <= params.centsTol, category: ( (tMs-curEvent.startMs)>=params.longMs ? 'long' : (inKey?'short_in':'other') ), note: targetLabel, midi: midiRounded, rms: currentRms, hz: f, confidence: lastPitch.confidence});

    renderLive({detectedLabel, hz:f, cents});
    updateCounters(params);

    rafId=requestAnimationFrame(loop);
  };

  rafId=requestAnimationFrame(loop);
}

async function stop(){
  if(!isRunning) return;
  const params=readParams();

  isRunning=false;
  UI.btnStart.disabled=false;
  UI.btnStop.disabled=true;

  if(rafId) cancelAnimationFrame(rafId);
  rafId=null;

  if(curEvent){
    const fin=finalizeEvent(curEvent, params);
    if(fin){
      if(!maybeMergeWithPrev(fin)) events.push(fin);
    }
    curEvent=null;
  }

  recordedBuffer = buildRecordedBuffer();

  if(procNode){
    try{ procNode.disconnect(); }catch(e){}
    procNode.onaudioprocess=null;
    procNode=null;
  }
  if(micStream){
    micStream.getTracks().forEach(t=>t.stop());
    micStream=null;
  }
  if(audioCtx){
    audioCtx.close();
    audioCtx=null;
  }

  UI.liveClass.textContent="已结束";
  renderLive(null);
  try{
    setAnalysisProgress(1, '开始', '正在准备分析…');
    events = await rebuildEventsOffline(params);
    renderReport(params);
  }catch(e){
    hideAnalysisProgress();
 console.error(e); alert('报告生成失败：'+(e && e.message ? e.message : e)); }
  if(typeof renderTrend==='function'){ try{ renderTrend(); }catch(e){} }
  if(UI.btnExportVideo) UI.btnExportVideo.disabled = !recordedBuffer;
}


function setTol(newVal){
  const v = Math.max(5, Math.min(50, Math.round(newVal/5)*5));
  UI.centsTol.value = String(v);
  if(UI.centsTolVal) UI.centsTolVal.textContent = String(v);
  // refresh dependent views
  if(typeof renderTrend==='function'){ try{ renderTrend(); }catch(e){} }
  renderTable();
  // scores depend on pass/fail, but we recompute pass only at finalize; for simplicity, refresh KPIs on report only.
}
if(UI.btnTolMinus){
  // init display
  if(UI.centsTolVal) UI.centsTolVal.textContent = UI.centsTol.value;
  UI.btnTolMinus.addEventListener("click", ()=> setTol(Number(UI.centsTol.value) - 5));
  UI.btnTolPlus.addEventListener("click", ()=> setTol(Number(UI.centsTol.value) + 5));
}


async function exportVideo(){
  if(!recordedBuffer || !pitchTimeline.length) return;

  const W = 1280, H = 720;
  const canvas = document.createElement("canvas");
  canvas.width = W; canvas.height = H;
  const g = canvas.getContext("2d");

  const fps = 30;
  const vStream = canvas.captureStream(fps);

  // Audio: recorded buffer into MediaStreamDestination (NO monitoring to speakers)
  const ctx = ensurePlayCtx();
  stopAudio();

  const dest = ctx.createMediaStreamDestination();
  const src = ctx.createBufferSource();
  src.buffer = recordedBuffer;

  const gain = ctx.createGain();
  gain.gain.value = 1.0; // 导出保持真实
  src.connect(gain);
  gain.connect(dest);

  // Merge streams
  const outStream = new MediaStream();
  vStream.getVideoTracks().forEach(t=>outStream.addTrack(t));
  dest.stream.getAudioTracks().forEach(t=>outStream.addTrack(t));

  const types = [
    "video/webm;codecs=vp9,opus",
    "video/webm;codecs=vp8,opus",
    "video/webm;codecs=vp9",
    "video/webm",
  ];
  let mime = "";
  for(const t of types){ if(MediaRecorder.isTypeSupported(t)){ mime=t; break; } }

  const rec = new MediaRecorder(outStream, mime?{mimeType:mime}:undefined);
  const chunks=[];
  rec.ondataavailable=(e)=>{ if(e.data && e.data.size) chunks.push(e.data); };

  const params = readParams();
  const k = computeKpis(params);
  const overall = Math.round(k.overallScore);
  const longS = Math.round(k.longScore);
  const shortS = Math.round(k.shortScore);
  const tol = params.centsTol;
  // Needle smoothing (visual only): makes motion linear & comfortable.
  const needleTauMs = 180;   // time constant (ms). higher = smoother/slower
  const hystCents = 2.0;     // pass/fail hysteresis (visual only) to avoid flicker
  let smoothCents = 0;
  let smoothInit = false;
  let lastPlayMs = 0;
  let visualPass = true;


  function lastTimelineAt(ms){
    let cur=pitchTimeline[0];
    for(const p of pitchTimeline){
      if(p.tMs<=ms) cur=p;
      else break;
    }
    return cur;
  }

  function drawHeader(){
    g.fillStyle="#eaeef7";
    g.font="900 32px ui-sans-serif, system-ui";
    g.fillText("TUNER ANALYSIS", 48, 58);

    g.fillStyle="#9aa3b2";
    g.font="700 18px ui-sans-serif, system-ui";
    g.fillText(`A4=${params.aRef}Hz  ·  阈值±${tol}c  ·  调性分类：${params.keyClass}大调`, 48, 92);
  }

  function drawScoreStrip(){
    const y = H-92;
    const x = 48;
    const w = W-96;
    const h = 54;

    g.fillStyle="#0f1117";
    g.strokeStyle="#232838";
    g.lineWidth=2;
    g.fillRect(x,y,w,h);
    g.strokeRect(x,y,w,h);

    const colW = (w-30)/3;
    const shortActive = (k.shortShare>0.20);

    function box(ix, title, val, active){
      const bx = x+15 + ix*(colW+5);
      g.fillStyle="#0b0c10";
      g.strokeStyle="#232838";
      g.lineWidth=2;
      g.fillRect(bx, y+8, colW, h-16);
      g.strokeRect(bx, y+8, colW, h-16);

      g.fillStyle="#9aa3b2";
      g.font="700 14px ui-sans-serif, system-ui";
      g.fillText(title, bx+14, y+28);

      g.fillStyle=active?"#eaeef7":"#9aa3b2";
      g.font="950 26px ui-sans-serif, system-ui";
      g.fillText(String(val), bx+14, y+52);
    }

    box(0, "综合分(100)", overall, true);
    box(1, "长音分", longS, true);
    box(2, "短音分", shortS, shortActive);
  }

  function drawTrendPanel(x,y,w,h, playMs, durMs){
    g.fillStyle="#0f1117";
    g.strokeStyle="#232838";
    g.lineWidth=2;
    g.fillRect(x,y,w,h);
    g.strokeRect(x,y,w,h);

    const inner = {x:x+18, y:y+22, w:w-36, h:h-44};
    const yCenter = inner.y + inner.h/2;
    const scale = (inner.h*0.42)/50;
    const yTol = tol*scale;

    g.globalAlpha=0.18;
    g.fillStyle="#6aa8ff";
    g.fillRect(inner.x, yCenter-yTol, inner.w, yTol*2);
    g.globalAlpha=1;

    g.globalAlpha=0.35;
    g.strokeStyle="#232838";
    g.lineWidth=1;
    for(const dy of [-50,-25,0,25,50]){
      const yy = yCenter - dy*scale;
      g.beginPath(); g.moveTo(inner.x, yy); g.lineTo(inner.x+inner.w, yy); g.stroke();
    }
    g.globalAlpha=1;

    const dt = Math.max(1, durMs);
    const maxC=50;
    const mapY = (c)=> yCenter - Math.max(-maxC, Math.min(maxC, c))*scale;
    const mapX = (t)=> inner.x + (t/dt)*inner.w;

    // line (up to playMs)
    g.strokeStyle="#eaeef7";
    g.lineWidth=2.5;
    g.globalAlpha=0.7;
    g.beginPath();
    let started=false;
    for(const p of pitchTimeline){
      if(p.tMs>playMs) break;
      const xx=mapX(p.tMs);
      const yy=mapY(p.cents);
      if(!started){ g.moveTo(xx,yy); started=true; }
      else g.lineTo(xx,yy);
    }
    if(started) g.stroke();
    g.globalAlpha=1;

    // current point
    const cur = lastTimelineAt(playMs);
    if(cur){
      const xx=mapX(playMs);
      const yy=mapY(cur.cents);
      g.fillStyle = cur.pass ? "#4ad27a" : "#ff5a6a";
      g.beginPath(); g.arc(xx,yy,5,0,Math.PI*2); g.fill();
    }

    // playhead
    const xh = mapX(playMs);
    g.strokeStyle="#9aa3b2";
    g.globalAlpha=0.6;
    g.lineWidth=2;
    g.beginPath(); g.moveTo(xh, inner.y); g.lineTo(xh, inner.y+inner.h); g.stroke();
    g.globalAlpha=1;

    g.fillStyle="#9aa3b2";
    g.font="700 14px ui-sans-serif, system-ui";
    g.fillText("音准趋势（cents）", x+18, y+18);
  }

  function drawTunerPanel(x,y,w,h, playMs, durMs){
    g.fillStyle="#0f1117";
    g.strokeStyle="#232838";
    g.lineWidth=2;
    g.fillRect(x,y,w,h);
    g.strokeRect(x,y,w,h);

    const cur = lastTimelineAt(playMs);
    const centsRaw = cur ? cur.cents : 0;
    // smoothCents already updated in drawFrame()
    const cents = smoothCents;
    const pass = visualPass;
    const note = cur ? cur.note : "—";

    g.fillStyle="#eaeef7";
    g.textAlign="center";
    g.font="950 110px ui-sans-serif, system-ui";
    g.fillText(note, x + w/2, y + 150);

    const pillW=260, pillH=64;
    const px = x + w/2 - pillW/2;
    const py = y + 182;
    g.fillStyle = pass ? "rgba(74,210,122,0.16)" : "rgba(255,90,106,0.16)";
    g.strokeStyle = pass ? "rgba(74,210,122,0.55)" : "rgba(255,90,106,0.55)";
    g.lineWidth=2;
    g.beginPath();
    const r=18;
    g.moveTo(px+r,py);
    g.arcTo(px+pillW,py,px+pillW,py+pillH,r);
    g.arcTo(px+pillW,py+pillH,px,py+pillH,r);
    g.arcTo(px,py+pillH,px,py,r);
    g.arcTo(px,py,px+pillW,py,r);
    g.closePath();
    g.fill(); g.stroke();

    g.fillStyle = pass ? "#4ad27a" : "#ff5a6a";
    g.font="900 46px ui-sans-serif, system-ui";
    const ct = `${cents>=0?"+":""}${cents.toFixed(1)}c`;
    g.fillText(ct, x + w/2, py + 48);

    const cx = x + w/2;
    const cy = y + h*0.70;
    const radius = Math.min(w, h)*0.36;

    const start = Math.PI * 1.08;
    const end   = Math.PI * -0.08;

    const maxC=50;
    const mapAngle = (c)=>{
      const cc = Math.max(-maxC, Math.min(maxC, c));
      const t = (cc + maxC) / (2*maxC);
      return start + (end-start)*t;
    };

    const aTolL = mapAngle(-tol);
    const aTolR = mapAngle(+tol);
    g.globalAlpha=0.30;
    g.strokeStyle="#4ad27a";
    g.lineWidth=18;
    g.beginPath();
    g.arc(cx,cy,radius,aTolL,aTolR,false);
    g.stroke();
    g.globalAlpha=1;

    g.strokeStyle="#232838";
    g.lineWidth=7;
    g.beginPath();
    g.arc(cx,cy,radius,start,end,false);
    g.stroke();

    g.globalAlpha=0.6;
    g.strokeStyle="#9aa3b2";
    g.lineWidth=2;
    for(let c=-50;c<=50;c+=10){
      const a=mapAngle(c);
      const r1=radius-6, r2=radius-22;
      const x1=cx+Math.cos(a)*r1, y1=cy+Math.sin(a)*r1;
      const x2=cx+Math.cos(a)*r2, y2=cy+Math.sin(a)*r2;
      g.beginPath(); g.moveTo(x1,y1); g.lineTo(x2,y2); g.stroke();
    }
    g.globalAlpha=1;

    const ang = mapAngle(cents);
    const nx = cx + Math.cos(ang)*(radius-34);
    const ny = cy + Math.sin(ang)*(radius-34);

    g.strokeStyle = pass ? "#4ad27a" : "#ff5a6a";
    g.lineWidth = 10;
    g.lineCap = "round";
    g.beginPath();
    g.moveTo(cx,cy);
    g.lineTo(nx,ny);
    g.stroke();

    g.fillStyle="#eaeef7";
    g.beginPath(); g.arc(cx,cy,12,0,Math.PI*2); g.fill();

    g.textAlign="left";
    g.fillStyle="#9aa3b2";
    g.font="700 16px ui-sans-serif, system-ui";
    g.fillText(`时间 ${(playMs/1000).toFixed(2)}s / ${(durMs/1000).toFixed(2)}s`, x+18, y+h-16);
  }

  function drawFrame(ms, finalCard=false){
    const durMs = recordedBuffer.duration*1000;
    const playMs = Math.max(0, Math.min(durMs, ms));

    // Update smoothing state (visual only)
    const curForSmooth = lastTimelineAt(playMs);
    const target = curForSmooth ? curForSmooth.cents : 0;
    const dtMs = Math.max(0, playMs - lastPlayMs);
    const a = dtMs<=0 ? 1.0 : (1 - Math.exp(-dtMs/needleTauMs));
    if(!smoothInit){ smoothCents = target; smoothInit = true; }
    else { smoothCents = smoothCents + (target - smoothCents)*a; }
    // Hysteresis for visual pass/fail (avoid flicker)
    const absC = Math.abs(smoothCents);
    if(visualPass){
      if(absC > tol + hystCents) visualPass = false;
    } else {
      if(absC <= Math.max(0, tol - hystCents)) visualPass = true;
    }
    lastPlayMs = playMs;

    g.fillStyle="#0b0c10";
    g.fillRect(0,0,W,H);

    drawHeader();

    const contentTop = 120;
    const contentBottom = H-110;
    const contentH = contentBottom - contentTop;

    const pad = 48;
    const gap = 16;
    const leftW = Math.floor((W - pad*2 - gap) * 0.52);
    const rightW = (W - pad*2 - gap) - leftW;
    const leftX = pad;
    const rightX = pad + leftW + gap;
    const y = contentTop;
    const h = contentH;

    drawTunerPanel(leftX, y, leftW, h, playMs, durMs);
    drawTrendPanel(rightX, y, rightW, h, playMs, durMs);

    drawScoreStrip();

    if(finalCard){
      g.fillStyle="rgba(0,0,0,0.55)";
      g.fillRect(0,0,W,H);

      g.fillStyle="#eaeef7";
      g.textAlign="left";
      g.font="950 72px ui-sans-serif, system-ui";
      g.fillText("最终得分", 70, 210);

      g.font="980 92px ui-sans-serif, system-ui";
      g.fillText(`综合分  ${overall}`, 70, 330);

      g.fillStyle="#9aa3b2";
      g.font="850 34px ui-sans-serif, system-ui";
      const modeTxt = (k.shortShare>0.20) ? "综合=长音 + 短音-调内(0.40权重)" : "综合=仅长音（短音≤20%不计入）";
      g.fillText(modeTxt, 70, 390);

      g.font="850 34px ui-sans-serif, system-ui";
      g.fillText(`长音 ${longS}    短音-调内 ${shortS}    其他 ${k.otherTotal}`, 70, 450);
    }
  }

  // progress UI
  const holdSec = 2.0;
  const totalMs = recordedBuffer.duration*1000 + holdSec*1000;

  function setProg(pct, title){
    if(!UI.exportProg) return;
    UI.exportProg.classList.remove("hidden");
    if(UI.exportProgTitle && title) UI.exportProgTitle.textContent = title;
    if(UI.exportProgPct) UI.exportProgPct.textContent = `${Math.round(pct)}%`;
    if(UI.exportBarFill) UI.exportBarFill.style.width = `${pct}%`;
  }

  let raf=0;
  let tStart=0;
  const durMs = recordedBuffer.duration*1000;

  function step(){
    const elapsedMs = (ctx.currentTime - tStart)*1000;
    const ms = Math.min(durMs, elapsedMs);
    drawFrame(ms,false);

    const pct = Math.max(0, Math.min(99, (elapsedMs/totalMs)*100));
    setProg(pct, "正在生成视频…");

    if(elapsedMs < durMs){
      raf = requestAnimationFrame(step);
    }
  }

  // start record
  rec.start(200);
  tStart = ctx.currentTime;
  setProg(0, "正在生成视频…");
  src.start();
  raf = requestAnimationFrame(step);

  await new Promise(res=>{ src.onended=()=>res(); });

  // final hold 2s (still updating progress)
  const holdStart = ctx.currentTime;
  await new Promise((resolve)=>{
    function hold(){
      drawFrame(durMs,true);
      const elapsedMs = (ctx.currentTime - tStart)*1000;
      const pct = Math.max(0, Math.min(100, (elapsedMs/totalMs)*100));
      setProg(pct, "正在生成视频…");
      if(ctx.currentTime - holdStart < holdSec) requestAnimationFrame(hold);
      else resolve();
    }
    hold();
  });

  rec.stop();
  cancelAnimationFrame(raf);

  const blob = await new Promise((resolve)=>{
    rec.onstop = ()=> resolve(new Blob(chunks, {type: mime||"video/webm"}));
  });

  setProg(100, "生成完成，开始下载…");

  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  const stamp = new Date().toISOString().replace(/[:.]/g,"-");
  a.href = url;
  a.download = `tuner-analysis-${stamp}.webm`;
  document.body.appendChild(a);
  a.click();
  a.remove();
  setTimeout(()=>URL.revokeObjectURL(url), 4000);

  // hide progress after a moment
  setTimeout(()=>{
    if(UI.exportProg) UI.exportProg.classList.add("hidden");
  }, 1200);
}

if(UI.btnExportVideo){
  UI.btnExportVideo.addEventListener("click", async ()=>{
    try{
      UI.btnExportVideo.disabled = true;
      await exportVideo();
    } catch(e){
      console.error(e);
      alert("导出失败：该浏览器可能不支持视频编码/MediaRecorder。建议用 Chrome/Edge 导出 WebM。");
    } finally {
      UI.btnExportVideo.disabled = !recordedBuffer;
    }
  });
}

UI.btnStart.addEventListener("click", async ()=>{
  try{ await start(); }
  catch(err){
    console.error(err);
    alert("无法启动麦克风：请确认权限已允许，并用 https 或 localhost 访问。");
    UI.btnStart.disabled=false;
    UI.btnStop.disabled=true;
  }
});
UI.btnStop.addEventListener("click", ()=>stop());


// ---------------- settings modal (UI only)
function setupSettingsModal(){
  const btn = document.getElementById("btnSettings");
  const modal = document.getElementById("settingsModal");
  const closeBtn = document.getElementById("btnSettingsClose");
  const backdrop = document.getElementById("settingsBackdrop");
  if(!btn || !modal || !closeBtn || !backdrop) return;

  const open = ()=>{
    modal.classList.remove("hidden");
    // Update summary values immediately
    try{ updateSettingsSummary(); }catch(e){}
  };
  const close = ()=> modal.classList.add("hidden");

  btn.addEventListener("click", open);
  closeBtn.addEventListener("click", close);
  backdrop.addEventListener("click", close);
  document.addEventListener("keydown",(e)=>{
    if(e.key==="Escape" && !modal.classList.contains("hidden")) close();
  });
}

function updateSettingsSummary(){
  const sumProfile = document.getElementById("sumProfile");
  const sumKey = document.getElementById("sumKey");
  const sumA4 = document.getElementById("sumA4");
  const sumTol = document.getElementById("sumTol");
  const elProfile = document.getElementById("inputProfile");
  const elKey = document.getElementById("keyClass");
  const elA4 = document.getElementById("aRef");
  const elTol = document.getElementById("centsTolVal") || document.getElementById("tolVal");
  const tolHidden = document.getElementById("centsTol");

  if(sumProfile && elProfile) sumProfile.textContent = elProfile.value === "voice" ? "人声" : "双簧管";
  if(sumKey && elKey) sumKey.textContent = elKey.value;
  if(sumA4 && elA4) sumA4.textContent = (elA4.value||"440") + "Hz";
  if(sumTol){
    const v = tolHidden ? Number(tolHidden.value) : (elTol ? Number(elTol.textContent) : 20);
    sumTol.textContent = "±" + (isFinite(v)?v:20) + "c";
  }
}

// Hook into existing UI init
window.addEventListener('DOMContentLoaded', ()=>{
  try{
    setupSettingsModal();
    // keep summary updated when user changes settings
    document.addEventListener('change', (e)=>{
      const id = e && e.target && e.target.id;
      if(["inputProfile","keyClass","aRef","centsTol"].includes(id)) updateSettingsSummary();
    });
    document.addEventListener('click', (e)=>{
      const id = e && e.target && e.target.id;
      if(["btnTolMinus","btnTolPlus"].includes(id)) setTimeout(updateSettingsSummary, 0);
    });
    setTimeout(updateSettingsSummary, 0);
  }catch(e){ console.error(e); }
});
// ---------------- offline segmentation (post analysis) with progress
function rollingMedian(arr, i, win){
  const s = Math.max(0, i-win+1);
  const slice = [];
  for(let k=s;k<=i;k++){
    const v = arr[k];
    if(Number.isFinite(v)) slice.push(v);
  }
  if(!slice.length) return NaN;
  slice.sort((a,b)=>a-b);
  const m = Math.floor(slice.length/2);
  return slice.length%2 ? slice[m] : (slice[m-1]+slice[m])/2;
}

function setAnalysisProgress(pct, sub, line){
  const wrap = document.getElementById("analysisProgressWrap");
  const pctEl = document.getElementById("analysisPct");
  const subEl = document.getElementById("analysisSub");
  const lineEl = document.getElementById("analysisLine");
  const fill = document.getElementById("analysisFill");
  if(!wrap||!pctEl||!subEl||!lineEl||!fill) return;
  wrap.classList.remove("hidden");
  const v = Math.max(0, Math.min(100, pct|0));
  pctEl.textContent = v + "%";
  subEl.textContent = sub || "分析中…";
  lineEl.textContent = line || "正在剪辑与校验音高…";
  fill.style.width = v + "%";
  wrap.style.setProperty("--deg", (v/100*360).toFixed(1)+"deg");
}
function hideAnalysisProgress(){
  const wrap = document.getElementById("analysisProgressWrap");
  if(wrap) wrap.classList.add("hidden");
}

async function rebuildEventsOffline(params){
  // Use pitchTimeline to rebuild note events after recording (reduces "two pitches in one note").
  const tlAll = (pitchTimeline||[]).filter(p=>p && Number.isFinite(p.tMs) && Number.isFinite(p.midi) && Number.isFinite(p.cents));
  if(tlAll.length < 3) return [];
  const minRms = 0.004;
  const gapMs = 70;
  const changeHoldMs = 90;     // must persist to commit note change
  const minKeepMs = 60;
  const minScoreMs = 110;      // short transitions won't score

  // Build arrays and smooth midi with rolling median
  setAnalysisProgress(5, "预处理", "平滑音高轨迹…");
  await new Promise(r=>setTimeout(r,0));

  const midiArr = tlAll.map(p=>p.midi);
  const win = 7;
  const smMidi = new Array(tlAll.length);
  for(let i=0;i<tlAll.length;i++){
    smMidi[i] = Math.round(rollingMedian(midiArr,i,win));
    if(i % 400 === 0){
      setAnalysisProgress(5 + Math.floor(i/tlAll.length*30), "预处理", "平滑音高轨迹…");
      await new Promise(r=>setTimeout(r,0));
    }
  }

  setAnalysisProgress(40, "剪辑中", "根据稳定音高切分音符…");
  await new Promise(r=>setTimeout(r,0));

  const events2 = [];
  let cur=null;
  let pending=null;

  function closeCur(endIdx){
    if(!cur) return;
    const endMs = tlAll[endIdx].tMs;
    const durMs = endMs - cur.startMs;
    if(durMs <= 0){ cur=null; return; }

    const slice = tlAll.slice(cur.startIdx, endIdx+1);
    const centsMed = median(slice.map(p=>p.cents));
    const hzMed = median(slice.map(p=>p.hz).filter(Number.isFinite));
    const confMean = mean(slice.map(p=>p.confidence).filter(Number.isFinite));
    const rmsMed = median(slice.map(p=>p.rms).filter(Number.isFinite));

    const midi = cur.midi;
    const note = slice[Math.floor(slice.length/2)].note || cur.note || "—";

    const inKey = isNoteInKey(midi, params.keyClass);
    let category = (durMs >= params.longMs) ? "long" : (inKey ? "short_in" : "other");

    const veryQuiet = Number.isFinite(rmsMed) && rmsMed < minRms;
    const extreme = Math.abs(centsMed) >= 40;

    if(veryQuiet && durMs >= 200) category = "other";
    if(extreme && (veryQuiet || confMean < 0.45)) category = "other";
    if(durMs < minScoreMs) category = "other";
    if(durMs < minKeepMs && (veryQuiet || confMean < 0.35)){ cur=null; return; }

    const pass = Math.abs(centsMed) <= params.centsTol;

    events2.push({
      startMs: Math.round(cur.startMs),
      endMs: Math.round(endMs),
      durMs: Math.round(durMs),
      detectedLabel: note,
      hz: hzMed,
      cents: centsMed,
      conf: confMean,
      inKey,
      category,
      pass,
    });
    cur=null;
  }

  for(let i=0;i<tlAll.length;i++){
    const p = tlAll[i];
    const m = smMidi[i];
    const isSilent = !Number.isFinite(p.rms) || p.rms < minRms;
    if(isSilent){
      if(cur){
        const prev = tlAll[i-1] || p;
        if(p.tMs - prev.tMs > gapMs) closeCur(i-1);
      }
      pending=null;
      continue;
    }
    if(!cur){
      cur = {startIdx:i, startMs:p.tMs, midi:m, note:p.note};
      pending=null;
      continue;
    }
    if(m === cur.midi){
      pending=null;
      continue;
    }
    if(!pending || pending.midi !== m){
      pending = {midi:m, sinceIdx:i, sinceMs:p.tMs};
      continue;
    }
    if(p.tMs - pending.sinceMs >= changeHoldMs){
      closeCur(i-1);
      cur = {startIdx: pending.sinceIdx, startMs: pending.sinceMs, midi: pending.midi, note: p.note};
      pending=null;
    }
    if(i % 350 === 0){
      setAnalysisProgress(40 + Math.floor(i/tlAll.length*40), "剪辑中", "根据稳定音高切分音符…");
      await new Promise(r=>setTimeout(r,0));
    }
  }
  if(cur) closeCur(tlAll.length-1);

  setAnalysisProgress(85, "整理中", "合并碎片并计算得分…");
  await new Promise(r=>setTimeout(r,0));

  // Merge adjacent identical notes separated by tiny gaps
  const merged=[];
  const mergeGap=50;
  for(const e of events2){
    const prev = merged[merged.length-1];
    if(prev && prev.detectedLabel===e.detectedLabel && (e.startMs - prev.endMs) <= mergeGap){
      prev.endMs = e.endMs;
      prev.durMs = prev.endMs - prev.startMs;
      prev.cents = (prev.cents*prev.durMs + e.cents*e.durMs) / (prev.durMs + e.durMs);
      prev.pass = Math.abs(prev.cents) <= params.centsTol;
      continue;
    }
    merged.push({...e});
  }
  setAnalysisProgress(100, "完成", "报告已生成");
  setTimeout(hideAnalysisProgress, 500);
  return merged;
}



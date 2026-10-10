/* GLITCH SURVIVAL — 2D REBOOT
   A self-contained top-down mobile survival game. No third-party JS or assets.
   All sprites are original procedural Canvas 2D artwork.
*/
(()=>{
'use strict';
const canvas=document.getElementById('world');
const ctx=canvas.getContext('2d',{alpha:false});
const $=id=>document.getElementById(id);
const SAVE_KEY='glitch-survival-2d-v1';
const WORLD_LIMIT=2750;
const TAU=Math.PI*2;
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
const distance=(ax,ay,bx,by)=>Math.hypot(ax-bx,ay-by);
const randHash=(x,y,s=0)=>{let z=Math.imul((x|0)+92837111,374761393)^Math.imul((y|0)+668265263,1274126177)^Math.imul(s+392017,1103515245);z^=z>>>13;z=Math.imul(z,1274126177);return ((z^(z>>>16))>>>0)/4294967296;};
const mulberry32=(seed)=>()=>{let t=seed+=0x6d2b79f5;t=Math.imul(t^t>>>15,t|1);t^=t+Math.imul(t^t>>>7,t|61);return ((t^t>>>14)>>>0)/4294967296};
const TYPES={
 wood:{name:'Wood',emoji:'🪵'},stone:{name:'Stone',emoji:'🪨'},fiber:{name:'Plant fiber',emoji:'🌿'},cloth:{name:'Cloth',emoji:'🧶'},scrap:{name:'Scrap',emoji:'⚙️'},leather:{name:'Leather',emoji:'🟫'},food:{name:'Canned food',emoji:'🥫'},water:{name:'Water',emoji:'💧'},bandage:{name:'Bandage',emoji:'✚'},
 axe:{name:'Stone axe',emoji:'🪓'},pickaxe:{name:'Stone pickaxe',emoji:'⛏️'},spear:{name:'Wood spear',emoji:'🗡️'},torch:{name:'Torch',emoji:'🔥'},shirt:{name:'Worn shirt',emoji:'👕'},hoodie:{name:'Scavenger hoodie',emoji:'🧥'},cargo:{name:'Cargo trousers',emoji:'👖'},boots:{name:'Worn boots',emoji:'🥾'},backpack:{name:'Small backpack',emoji:'🎒'}
};
const RECIPES=[
 {id:'axe',type:'tool',desc:'Fast tree chopping. Shows in your hand.',cost:{wood:3,stone:2,fiber:1}},
 {id:'pickaxe',type:'tool',desc:'Mine rocks for extra stone.',cost:{wood:3,stone:3,fiber:2}},
 {id:'spear',type:'tool',desc:'Long reach against the infected.',cost:{wood:4,fiber:3,stone:1}},
 {id:'torch',type:'tool',desc:'Light up the night.',cost:{wood:2,fiber:2}},
 {id:'cloth',type:'material',desc:'Weave plant fibers into basic cloth.',cost:{fiber:3}},
 {id:'bandage',type:'medical',desc:'Restores 38 health when used.',cost:{fiber:3,cloth:1}},
 {id:'shirt',type:'clothing',desc:'Wearable shirt. +4% protection.',cost:{cloth:3,fiber:2}},
 {id:'hoodie',type:'clothing',desc:'Scavenger hoodie. +10% protection.',cost:{cloth:6,scrap:2}},
 {id:'cargo',type:'clothing',desc:'Cargo pants. +5% protection.',cost:{cloth:4,fiber:3}},
 {id:'boots',type:'clothing',desc:'Sturdy boots. +5% protection.',cost:{cloth:3,leather:2}},
 {id:'backpack',type:'clothing',desc:'Visible on your back. +20 carry capacity.',cost:{cloth:4,fiber:3,scrap:1}}
];
const RECIPE_BY_ID=Object.fromEntries(RECIPES.map(r=>[r.id,r]));
const BUILD_RECIPES=[
 {id:'wall',name:'Wooden wall',emoji:'🪵',desc:'Blocks zombies and marks out your base.',cost:{wood:5}},
 {id:'floor',name:'Wood floor',emoji:'▦',desc:'Lays a sturdy foundation.',cost:{wood:3}},
 {id:'campfire',name:'Campfire',emoji:'🔥',desc:'A warm point of light in the dark.',cost:{wood:4,stone:3}},
 {id:'storage',name:'Storage crate',emoji:'📦',desc:'Useful base furnishing.',cost:{wood:6,stone:2}}
];
const MAX_TOOL_USES={axe:28,pickaxe:28,spear:40,torch:65};
let viewport={w:1,h:1,dpr:1,scale:1};
let camera={x:0,y:0};
let gameOver=false,paused=false,modal=null,toastTimeout=0,hitFlash=0,screenShake=0,autosaveClock=0,enemySpawnClock=0,updateClock=0;
const effects=[];
const keys=new Set();
const joy={x:0,y:0,pointer:null};
let nodes=[],zombies=[],buildings=[];
let nextZombieId=0;
const state={player:{x:0,y:55,dir:0,anim:0,attacking:0,attackCooldown:0,hurt:0,footstep:0},hp:100,hunger:96,thirst:96,stamina:100,
 inventory:{wood:0,stone:0,fiber:0,cloth:0,scrap:0,leather:0,food:2,water:2,bandage:1,axe:0,pickaxe:0,spear:0,torch:0,shirt:0,hoodie:0,cargo:0,boots:0,backpack:0},
 equipment:{hand:null,chest:null,legs:'shorts',feet:'sandals',back:null},durability:{},elapsed:0,kills:0,treesCut:0,wallsBuilt:0,lootOpened:0,crafted:0,deathCount:0,flags:{},tutorialStep:0};

// A deterministic world: trees, rocks, crates and fiber bushes have stable IDs for saves.
function createWorld(){
 const rng=mulberry32(870223);
 nodes=[];
 const spacing=155;
 let id=0;
 for(let row=-18;row<=18;row++)for(let col=-18;col<=18;col++){
  const gx=col*spacing,gy=row*spacing;
  if(Math.hypot(gx,gy)<185)continue;
  const roll=rng();
  const kind=roll<.36?'tree':roll<.50?'rock':roll<.66?'bush':roll<.695?'crate':null;
  if(!kind)continue;
  const x=gx+(rng()-.5)*108,y=gy+(rng()-.5)*106;
  const size=(kind==='tree'?26:kind==='rock'?21:kind==='bush'?20:21)*(0.75+rng()*.48);
  nodes.push({id:'n'+id++,kind,x,y,size,variant:Math.floor(rng()*100),hp:kind==='tree'?3:kind==='rock'?3:kind==='bush'?1:1,maxhp:kind==='tree'?3:kind==='rock'?3:1,regenAt:0});
 }
 // Resource patch guaranteed near the starting clearing, away from the fire.
 const starters=[['tree',-164,-115],['tree',214,-35],['tree',-205,104],['tree',175,187],['rock',-105,-192],['rock',190,-185],['rock',-212,205],['bush',-95,158],['bush',66,-200],['bush',255,124],['crate',290,-83],['crate',-310,-42],['bush',-260,-220]];
 for(const [kind,x,y] of starters){let size=kind==='tree'?29:kind==='rock'?22:20;let hp=kind==='tree'||kind==='rock'?3:1;nodes.push({id:'s'+id++,kind,x,y,size,variant:id%19,hp,maxhp:hp,regenAt:0})}
 buildings=[{id:'starter-camp',kind:'campfire',x:0,y:-65,starter:true}];
 const zrng=mulberry32(320919);
 zombies=[];
 for(let n=0;n<33;n++){
  const angle=zrng()*TAU,rad=370+zrng()*1920;
  addZombie(Math.cos(angle)*rad,Math.sin(angle)*rad,true);
 }
}
function addZombie(x,y,persisted=false){
 const z={id:'z'+nextZombieId++,x,y,spawnX:x,spawnY:y,hp:3,maxhp:3,dir:0,walk:0,attackCooldown:Math.random()*1.1,stagger:0,deadUntil:0,aggro:0,persisted};
 zombies.push(z);return z;
}
function nodeActive(n){return !n.regenAt||n.regenAt<=state.elapsed}
function nearbyNode(max=84){let best=null,bestD=max;for(const n of nodes){if(!nodeActive(n))continue;let d=distance(state.player.x,state.player.y,n.x,n.y);if(d<bestD){best=n;bestD=d}}return best}
function nearbyZombie(max=95){let best=null,bestD=max;for(const z of zombies){if(z.deadUntil>state.elapsed||z.hp<=0)continue;let d=distance(state.player.x,state.player.y,z.x,z.y);if(d<bestD){best=z;bestD=d}}return best}
function resourceText(cost){return Object.entries(cost).map(([id,amount])=>`${TYPES[id]?.emoji||'▪'} ${amount}`).join('  ')}
function hasCost(cost){return Object.entries(cost).every(([k,n])=>(state.inventory[k]||0)>=n)}
function consumeCost(cost){if(!hasCost(cost))return false;for(const [k,n] of Object.entries(cost))state.inventory[k]-=n;return true}
function addItem(id,amount){if(!state.inventory.hasOwnProperty(id))return;state.inventory[id]+=amount;flashItem(id,amount)}
function flashItem(id,amount){effects.push({kind:'text',x:state.player.x,y:state.player.y-39,t:0,life:1.15,text:`+${amount} ${TYPES[id]?.name||id}`,color:'#d7ffd0'})}
function showToast(text,duration=2400){const el=$('toast');el.textContent=text;el.classList.add('show');clearTimeout(toastTimeout);toastTimeout=setTimeout(()=>el.classList.remove('show'),duration)}
function setMission(){let msg='';if((state.inventory.axe||0)===0 && state.equipment.hand!=='axe')msg='CRAFT A STONE AXE · gather wood, stone and fiber';else if(state.treesCut<2)msg='CHOP TWO TREES · equip your axe, then GATHER';else if(state.wallsBuilt<1)msg='BUILD A WALL · open BUILD when you have 5 wood';else if(state.kills<2)msg='SURVIVE · defeat 2 infected';else msg='BUILD YOUR BASE · explore, loot and survive the night';$('mission-text').textContent=msg}
function status(){const d=1+Math.floor(state.elapsed/600);let mins=(6*60+Math.floor((state.elapsed%600)/600*24*60))%(24*60);let hh=String(Math.floor(mins/60)).padStart(2,'0'),mm=String(mins%60).padStart(2,'0');$('day-label').textContent='DAY '+String(d).padStart(2,'0');$('time-label').textContent=hh+':'+mm;$('weather-label').textContent=(mins<350||mins>1150)?'☾ NIGHT':'☀ CLEAR';for(const [name,value] of [['hp',state.hp],['hunger',state.hunger],['thirst',state.thirst],['stamina',state.stamina]]){$(name+'-bar').style.width=clamp(value,0,100)+'%';$(name+'-label').textContent=Math.ceil(value)}
 $('quick-food').textContent=state.inventory.food;$('quick-water').textContent=state.inventory.water;$('quick-bandage').textContent=state.inventory.bandage;$('quick-axe').textContent=state.inventory.axe;$('quick-spear').textContent=state.inventory.spear;
 document.querySelectorAll('.quick-slot').forEach(el=>el.classList.toggle('selected',(el.dataset.quick==='3'&&state.equipment.hand==='axe')||(el.dataset.quick==='4'&&state.equipment.hand==='spear')));
 setMission();
}
function saveGame(silent=true){
 try{
  const save={version:1,elapsed:state.elapsed,player:{x:state.player.x,y:state.player.y,dir:state.player.dir},hp:state.hp,hunger:state.hunger,thirst:state.thirst,stamina:state.stamina,inventory:state.inventory,equipment:state.equipment,durability:state.durability,kills:state.kills,treesCut:state.treesCut,wallsBuilt:state.wallsBuilt,lootOpened:state.lootOpened,crafted:state.crafted,deathCount:state.deathCount,flags:state.flags,
   nodes:nodes.filter(n=>n.hp!==n.maxhp||n.regenAt>state.elapsed).map(n=>[n.id,n.hp,n.regenAt]),buildings:buildings.filter(b=>!b.starter),deadZombies:zombies.filter(z=>z.deadUntil>state.elapsed).map(z=>[z.id,z.deadUntil]),nextZombieId};
  localStorage.setItem(SAVE_KEY,JSON.stringify(save));$('save-indicator').textContent='● SAVED';if(!silent)showToast('Progress saved to this device');return true;
 }catch(e){console.warn('Save failed',e);$('save-indicator').textContent='○ SAVE UNAVAILABLE';return false}
}
function loadGame(){let raw;try{raw=localStorage.getItem(SAVE_KEY)}catch(e){return false}if(!raw)return false;try{
 const obj=JSON.parse(raw);if(obj.version!==1||!obj.player||typeof obj.player.x!=='number')return false;
 const numbers=['elapsed','hp','hunger','thirst','stamina','kills','treesCut','wallsBuilt','lootOpened','crafted','deathCount'];
 for(const k of numbers)if(Number.isFinite(obj[k]))state[k]=Math.max(0,obj[k]);
 state.hp=clamp(state.hp,0,100);state.hunger=clamp(state.hunger,0,100);state.thirst=clamp(state.thirst,0,100);state.stamina=clamp(state.stamina,0,100);
 state.player.x=clamp(obj.player.x,-WORLD_LIMIT,WORLD_LIMIT);state.player.y=clamp(obj.player.y,-WORLD_LIMIT,WORLD_LIMIT);state.player.dir=Number.isFinite(obj.player.dir)?obj.player.dir:0;
 for(const k of Object.keys(state.inventory))if(Number.isFinite(obj.inventory?.[k]))state.inventory[k]=clamp(Math.floor(obj.inventory[k]),0,9999);
 const valid={hand:[null,'axe','pickaxe','spear','torch'],chest:[null,'shirt','hoodie'],legs:['shorts','cargo'],feet:['sandals','boots'],back:[null,'backpack']};
 for(const k of Object.keys(valid)){let value=obj.equipment?.[k];if(valid[k].includes(value))state.equipment[k]=value}
 for(const k of Object.keys(MAX_TOOL_USES))if(Number.isFinite(obj.durability?.[k]))state.durability[k]=clamp(Math.floor(obj.durability[k]),0,MAX_TOOL_USES[k]);
 const nodeMap=new Map(nodes.map(n=>[n.id,n]));if(Array.isArray(obj.nodes))for(const [id,hp,regenAt] of obj.nodes){const n=nodeMap.get(id);if(n){n.hp=clamp(Number(hp)||0,0,n.maxhp);n.regenAt=Math.max(0,Number(regenAt)||0)}}
 if(Array.isArray(obj.buildings))buildings.push(...obj.buildings.filter(b=>b&&['wall','floor','campfire','storage'].includes(b.kind)&&Number.isFinite(b.x)&&Number.isFinite(b.y)&&Math.abs(b.x)<WORLD_LIMIT&&Math.abs(b.y)<WORLD_LIMIT).slice(0,400));
 const deadMap=new Map(Array.isArray(obj.deadZombies)?obj.deadZombies:[]);for(const z of zombies){const t=deadMap.get(z.id);if(Number.isFinite(t)&&t>state.elapsed){z.deadUntil=t;z.hp=0}}
 state.flags=(obj.flags&&typeof obj.flags==='object')?obj.flags:{};
 if(state.hp<=0){state.hp=80;state.player.x=0;state.player.y=60}
 camera.x=state.player.x;camera.y=state.player.y;
 return true;
 }catch(e){console.warn('Ignoring invalid save',e);return false}}
function hurtPlayer(raw){if(state.player.hurt>.1)return;const protection=(state.equipment.chest==='hoodie'?.13:state.equipment.chest==='shirt'?.05:0)+(state.equipment.legs==='cargo'?.05:0)+(state.equipment.feet==='boots'?.05:0);const dmg=Math.max(1,raw*(1-protection));state.hp=Math.max(0,state.hp-dmg);state.player.hurt=.52;hitFlash=.48;screenShake=6;effects.push({kind:'text',x:state.player.x,y:state.player.y-27,text:'-'+Math.ceil(dmg),color:'#ff8880',t:0,life:1});if(state.hp<=0)die()}
function die(){gameOver=true;joy.x=joy.y=0;keys.clear();$('death-screen').classList.remove('hidden');$('death-stats').textContent=`DAY ${Math.floor(state.elapsed/600)+1}  •  ${state.kills} KILLS  •  ${state.treesCut} TREES CUT`;saveGame();}
function respawn(){state.hp=100;state.hunger=Math.max(state.hunger,56);state.thirst=Math.max(state.thirst,56);state.stamina=100;state.player.x=0;state.player.y=55;state.deathCount++;state.player.hurt=1.25;gameOver=false;$('death-screen').classList.add('hidden');for(const z of zombies)if(z.hp>0&&distance(0,0,z.x,z.y)<240){z.x=z.spawnX;z.y=z.spawnY}saveGame();showToast('Respawned at camp. Your base and gear are safe.');}
function useSupply(id){if((state.inventory[id]||0)<1){showToast(`No ${TYPES[id]?.name||id} left`);return}if(id==='food'&&state.hunger>=99||id==='water'&&state.thirst>=99||id==='bandage'&&state.hp>=99){showToast('You do not need that yet');return}state.inventory[id]--;if(id==='food')state.hunger=clamp(state.hunger+38,0,100);if(id==='water')state.thirst=clamp(state.thirst+46,0,100);if(id==='bandage')state.hp=clamp(state.hp+38,0,100);showToast(`Used ${TYPES[id].name}`);status();saveGame()}
function equip(id){if(!TYPES[id])return;const slot=['axe','pickaxe','spear','torch'].includes(id)?'hand':['shirt','hoodie'].includes(id)?'chest':id==='cargo'?'legs':id==='boots'?'feet':id==='backpack'?'back':null;if(!slot)return;if((state.inventory[id]||0)<1){showToast(`Craft or find ${TYPES[id].name} first`);return}
 const current=state.equipment[slot];state.equipment[slot]=current===id?(slot==='legs'?'shorts':slot==='feet'?'sandals':null):id;if(slot==='hand'&&!state.durability[id])state.durability[id]=MAX_TOOL_USES[id];showToast(state.equipment[slot]===id?`Equipped ${TYPES[id].name}`:`Unequipped ${TYPES[id].name}`);status();if(modal)renderModal();saveGame()}
function toolWear(id,cost=1){if(state.equipment.hand!==id)return;let d=state.durability[id]??MAX_TOOL_USES[id];d-=cost;if(d<=0){state.inventory[id]=Math.max(0,state.inventory[id]-1);if(state.inventory[id]>0){d=MAX_TOOL_USES[id];showToast(`${TYPES[id].name} broke · using a spare`)}else{d=0;state.equipment.hand=null;showToast(`${TYPES[id].name} broke. Craft another.`)}}state.durability[id]=d}
function craft(id){const recipe=RECIPE_BY_ID[id];if(!recipe)return;if(!consumeCost(recipe.cost)){showToast('Not enough resources to craft '+TYPES[id].name);return}addItem(id,1);state.crafted++;if(['axe','pickaxe','spear','torch'].includes(id)){if(!state.durability[id])state.durability[id]=MAX_TOOL_USES[id];if(!state.equipment.hand)state.equipment.hand=id;}showToast(`Crafted ${TYPES[id].name}!${state.equipment.hand===id?' Equipped':''}`);status();renderModal();saveGame()}
function canPlaceAt(x,y){if(Math.abs(x)>WORLD_LIMIT-50||Math.abs(y)>WORLD_LIMIT-50)return false;if(distance(x,y,0,-65)<36)return false;for(const b of buildings)if(distance(x,y,b.x,b.y)<47)return false;for(const n of nodes)if(nodeActive(n)&&['tree','rock'].includes(n.kind)&&distance(x,y,n.x,n.y)<n.size+29)return false;return true}
function placeBuilding(id){const recipe=BUILD_RECIPES.find(r=>r.id===id);if(!recipe)return;if(!hasCost(recipe.cost)){showToast(`Need ${resourceText(recipe.cost)} to build ${recipe.name}`);return}
 const p=state.player,dist=68;const x=Math.round((p.x+Math.sin(p.dir)*dist)/54)*54,y=Math.round((p.y-Math.cos(p.dir)*dist)/54)*54;
 if(!canPlaceAt(x,y)){showToast('Move to a clear spot to place this structure');return}
 consumeCost(recipe.cost);buildings.push({id:'b'+Date.now()+'-'+buildings.length,kind:id,x,y});if(id==='wall')state.wallsBuilt++;showToast(`${recipe.name} placed!`);status();renderModal();saveGame()}
function gather(){if(paused||gameOver)return;const n=nearbyNode(92);if(!n){const z=nearbyZombie(81);if(z){attack();return}showToast('Move closer to a tree, rock, bush or crate');return}
 const p=state.player;p.dir=Math.atan2(n.x-p.x,-(n.y-p.y));p.attacking=.33;p.attackCooldown=Math.max(p.attackCooldown,.23);
 effects.push({kind:'slash',x:n.x,y:n.y,t:0,life:.22,angle:p.dir,color:'#e6e2c1'});
 if(n.kind==='crate'){
  const chance=randHash(n.variant,Math.floor(state.elapsed)+1,180);
  const loot={food:1+(chance>.65?1:0),water:1,cloth:1+(chance>.52?1:0),scrap:1};
  if(chance>.72)loot.bandage=1;if(chance>.87)loot.shirt=1;
  for(const [id,count] of Object.entries(loot))addItem(id,count);
  n.hp=0;n.regenAt=state.elapsed+240;state.lootOpened++;showToast('Supply crate looted! Open your backpack.');
 }else{
  const tool=state.equipment.hand;
  if(n.kind==='tree'&&tool==='axe'||n.kind==='rock'&&tool==='pickaxe'){n.hp-=2;toolWear(tool,1)}else n.hp-=1;
  if(n.hp<=0){
   const resource=n.kind==='tree'?'wood':n.kind==='rock'?'stone':'fiber';let count=n.kind==='tree'?(tool==='axe'?5:3):n.kind==='rock'?(tool==='pickaxe'?4:2):3;
   addItem(resource,count);n.hp=0;n.regenAt=state.elapsed+(n.kind==='tree'?155:n.kind==='rock'?185:75);if(n.kind==='tree')state.treesCut++;showToast(`${n.kind==='tree'?'Tree chopped':n.kind==='rock'?'Rock mined':'Plant harvested'} · +${count} ${TYPES[resource].name}`);
   effects.push({kind:'burst',x:n.x,y:n.y,t:0,life:.5,color:n.kind==='tree'?'#90b369':'#d6c5a0'});
  }else showToast(n.kind==='tree'?(tool==='axe'?'Chopping tree…':'Gathering fallen branches…'):n.kind==='rock'?'Mining stone…':'Gathering fiber…',900)
 }
 status();saveGame();
}
function attack(){if(paused||gameOver)return;const p=state.player;if(p.attackCooldown>0)return;const hand=state.equipment.hand;let range=hand==='spear'?110:hand==='axe'?76:64;let z=nearbyZombie(range);p.attacking=.35;p.attackCooldown=hand==='spear'?.67:.48;state.stamina=Math.max(0,state.stamina-4);
 if(z){p.dir=Math.atan2(z.x-p.x,-(z.y-p.y));let damage=hand==='spear'?2.2:hand==='axe'?1.75:hand==='pickaxe'?1.45:1;z.hp-=damage;z.stagger=.34;z.x+=(z.x-p.x)/(distance(z.x,z.y,p.x,p.y)||1)*16;z.y+=(z.y-p.y)/(distance(z.x,z.y,p.x,p.y)||1)*16;
  effects.push({kind:'text',x:z.x,y:z.y-29,t:0,life:.8,text:`-${Math.ceil(damage)}`,color:'#ffbc99'});
  if(['axe','pickaxe','spear'].includes(hand))toolWear(hand,1);
  if(z.hp<=0){z.hp=0;z.deadUntil=state.elapsed+165;state.kills++;addItem('scrap',1);if(randHash(Math.floor(z.spawnX),Math.floor(z.spawnY),14)>.32)addItem('cloth',1);if(randHash(Math.floor(z.spawnX),Math.floor(z.spawnY),14)>.70)addItem('leather',1);showToast('Infected defeated! Scavenge what you can.');}
 }else{if(hand==='spear'||hand==='axe')toolWear(hand,1);showToast('No infected in range',700)}
 effects.push({kind:'slash',x:p.x+Math.sin(p.dir)*33,y:p.y-Math.cos(p.dir)*33,t:0,life:.26,angle:p.dir,color:hand==='torch'?'#ffae65':'#ffefcd'});status();
}
function useQuick(index){if(index===0)useSupply('food');else if(index===1)useSupply('water');else if(index===2)useSupply('bandage');else if(index===3)equip('axe');else if(index===4)equip('spear')}

// Menus use static recipe definitions; player-controlled text is never injected.
function itemCards(inventory=false){const all=Object.keys(TYPES);return all.filter(id=>inventory?state.inventory[id]>0:true).map(id=>{
 const info=TYPES[id];const qty=state.inventory[id]||0;return `<div class="item-card"><div class="item-top"><div class="item-emoji">${info.emoji}</div><div><div class="item-title">${info.name}</div><div class="item-cost">IN BAG: ${qty}</div></div></div><div class="item-desc">${inventory?itemDetails(id):''}</div>${inventory&&['axe','pickaxe','spear','torch','shirt','hoodie','cargo','boots','backpack'].includes(id)?`<button class="small-btn" data-equip="${id}">${Object.values(state.equipment).includes(id)?'UNEQUIP':'EQUIP'}</button>`:inventory&&['food','water','bandage'].includes(id)?`<button class="small-btn" data-use="${id}">USE</button>`:''}</div>`;
 }).join('')}
function itemDetails(id){if(['axe','pickaxe','spear','torch'].includes(id))return `Tool durability: ${state.durability[id]||MAX_TOOL_USES[id]} / ${MAX_TOOL_USES[id]}`;if(id==='shirt')return 'Basic chest protection.';if(id==='hoodie')return 'Better chest protection.';if(id==='cargo')return 'Leg protection.';if(id==='boots')return 'Sturdy footwear.';if(id==='backpack')return 'Extra storage space.';if(id==='food')return 'Restores hunger.';if(id==='water')return 'Restores thirst.';if(id==='bandage')return 'Restores health.';return 'Use this material to craft and build.'}
function listResources(){return ['wood','stone','fiber','cloth','scrap','leather'].map(id=>`<span class="resource-chip">${TYPES[id].emoji} ${TYPES[id].name} <span class="accent-text">${state.inventory[id]}</span></span>`).join('')}
function renderModal(){if(!modal)return;$('modal-title').textContent={inventory:'Backpack',craft:'Crafting bench',build:'Build your base',gear:'Survivor equipment',settings:'Game & saves'}[modal]||'Survival';document.querySelectorAll('.modal-tab').forEach(t=>t.classList.toggle('current',t.dataset.tab===modal));const body=$('modal-content');
 if(modal==='inventory')body.innerHTML=`<p class="panel-note">Everything you collect stays here. Equip clothing and tools to change how your survivor looks and fights.</p><div class="section-title">SUPPLIES & EQUIPMENT</div><div class="items-grid">${itemCards(true)}</div><p class="field-help">Quick-use food, water, bandages, axe and spear from the bottom hotbar.</p>`;
 if(modal==='craft')body.innerHTML=`<p class="panel-note">Collect resources, craft survival tools, and wear the gear you make. An equipped axe chops trees faster.</p><div class="resources">${listResources()}</div><div class="items-grid">${RECIPES.map(r=>`<div class="item-card"><div class="item-top"><div class="item-emoji">${TYPES[r.id].emoji}</div><div class="item-title">${TYPES[r.id].name}</div></div><div class="item-desc">${r.desc}</div><div class="item-cost">${resourceText(r.cost)}</div><button class="small-btn" data-craft="${r.id}" ${hasCost(r.cost)?'':'disabled'}>CRAFT ITEM</button></div>`).join('')}</div>`;
 if(modal==='build')body.innerHTML=`<p class="panel-note">Structures are placed <strong>in front of your survivor</strong>. Face an open patch of ground, then tap PLACE. Your buildings are saved.</p><div class="resources">${listResources()}</div><div class="items-grid">${BUILD_RECIPES.map(r=>`<div class="item-card"><div class="item-top"><div class="item-emoji">${r.emoji}</div><div class="item-title">${r.name}</div></div><div class="item-desc">${r.desc}</div><div class="item-cost">${resourceText(r.cost)}</div><button class="small-btn" data-build="${r.id}" ${hasCost(r.cost)?'':'disabled'}>PLACE IN WORLD</button></div>`).join('')}</div>`;
 if(modal==='gear'){
 const display={hand:state.equipment.hand?TYPES[state.equipment.hand].name:'Bare hands',chest:state.equipment.chest?TYPES[state.equipment.chest].name:'Bare chest',legs:state.equipment.legs==='shorts'?'Ragged shorts':'Cargo trousers',feet:state.equipment.feet==='sandals'?'Worn sandals':'Worn boots',back:state.equipment.back?'Small backpack':'None'};
 const gearItems=['axe','pickaxe','spear','torch','shirt','hoodie','cargo','boots','backpack'].filter(id=>state.inventory[id]>0);
 body.innerHTML=`<p class="panel-note">Starter survivor: rugged hair, bare chest, ragged shorts and sandals. Equipping clothes or weapons changes your character in the game.</p><div class="equipment-grid">${Object.entries(display).map(([slot,value])=>`<div class="gear-slot"><strong>${slot.toUpperCase()}</strong><span>${value}</span></div>`).join('')}</div><div class="section-title">AVAILABLE GEAR</div><div class="items-grid">${gearItems.length?gearItems.map(id=>`<div class="item-card"><div class="item-top"><div class="item-emoji">${TYPES[id].emoji}</div><div class="item-title">${TYPES[id].name}</div></div><div class="item-desc">${itemDetails(id)}</div><button class="small-btn" data-equip="${id}">${Object.values(state.equipment).includes(id)?'UNEQUIP':'EQUIP'}</button></div>`).join(''):'<p class="panel-note">No crafted clothes yet. Gather supplies and open CRAFTING to make some.</p>'}</div>`;
 }
 if(modal==='settings')body.innerHTML=`<p class="panel-note">Your game saves automatically to this browser. This is a fresh 2D game, separate from the previous 3D version.</p><div class="items-grid"><div class="item-card"><div class="item-title">SAVE GAME</div><div class="item-desc">Store character, inventory, health, buildings and world progress.</div><button class="small-btn" data-save="true">SAVE NOW</button></div><div class="item-card"><div class="item-title">CONTROLS</div><div class="item-desc">Phone: move joystick, GATHER, ATTACK, menus. Computer: WASD/arrows, E, Space, I, C, B, G.</div></div><div class="item-card"><div class="item-title">FRESH START</div><div class="item-desc">Erase this 2D world's progress on this device. Does not touch archived 3D backups.</div><button class="small-btn secondary" data-reset="true">RESET 2D SAVE</button></div></div>`;
}
function openModal(name){modal=name;paused=true;$('modal-shell').classList.remove('hidden');renderModal();joy.x=0;joy.y=0;}
function closeModal(){modal=null;paused=false;$('modal-shell').classList.add('hidden');status()}
function handleModalAction(e){const btn=e.target.closest('button');if(!btn)return;if(btn.dataset.craft)craft(btn.dataset.craft);else if(btn.dataset.build){placeBuilding(btn.dataset.build);renderModal()}else if(btn.dataset.equip)equip(btn.dataset.equip);else if(btn.dataset.use){useSupply(btn.dataset.use);renderModal()}else if(btn.dataset.save){saveGame(false);renderModal()}else if(btn.dataset.reset){if(confirm('Erase ONLY this new 2D save and start again?')){try{localStorage.removeItem(SAVE_KEY)}catch(e){}location.reload()}}}

// Canvas 2D rendering: world, vegetation, survivor, zombies and build pieces.
function resize(){const rect=canvas.getBoundingClientRect();viewport.w=Math.max(1,rect.width);viewport.h=Math.max(1,rect.height);viewport.dpr=Math.min(window.devicePixelRatio||1,2);viewport.scale=viewport.w<480?.95:viewport.h<460?1:1.12;canvas.width=Math.round(viewport.w*viewport.dpr);canvas.height=Math.round(viewport.h*viewport.dpr);ctx.setTransform(viewport.dpr,0,0,viewport.dpr,0,0);ctx.imageSmoothingEnabled=true}
const px=x=>(x-camera.x)*viewport.scale+viewport.w/2;
const py=y=>(y-camera.y)*viewport.scale+viewport.h/2;
function color(c){ctx.fillStyle=c}
function ellipse(x,y,rx,ry,fill,rot=0){ctx.beginPath();ctx.ellipse(x,y,rx,ry,rot,0,TAU);ctx.fillStyle=fill;ctx.fill()}
function polygon(points,fill,stroke){ctx.beginPath();ctx.moveTo(points[0][0],points[0][1]);for(let i=1;i<points.length;i++)ctx.lineTo(points[i][0],points[i][1]);ctx.closePath();if(fill){ctx.fillStyle=fill;ctx.fill()}if(stroke){ctx.strokeStyle=stroke;ctx.stroke()}}
function roundRect(x,y,w,h,r,fill,stroke){if(w<=0||h<=0)return;ctx.beginPath();ctx.roundRect(x,y,w,h,r);if(fill){ctx.fillStyle=fill;ctx.fill()}if(stroke){ctx.strokeStyle=stroke;ctx.lineWidth=1;ctx.stroke()}}
function drawGround(){const {w,h,scale}=viewport;ctx.fillStyle='#738c58';ctx.fillRect(0,0,w,h);const tile=86;const minX=Math.floor((camera.x-w/(2*scale))/tile)-1,maxX=Math.floor((camera.x+w/(2*scale))/tile)+1;const minY=Math.floor((camera.y-h/(2*scale))/tile)-1,maxY=Math.floor((camera.y+h/(2*scale))/tile)+1;
 for(let yy=minY;yy<=maxY;yy++)for(let xx=minX;xx<=maxX;xx++){
  const x=px(xx*tile),y=py(yy*tile),size=tile*scale+.5;
  let r=randHash(xx,yy),tone=r>.83?'#6e8854':r>.56?'#77915e':r>.32?'#738c58':'#728855';ctx.fillStyle=tone;ctx.fillRect(x,y,size,size);
  const n=randHash(xx,yy,49);if(n>.75){ctx.fillStyle='#92945d1b';ctx.fillRect(x+size*.24,y+size*.15,size*.55,size*.42)}
  // Faint grass brush clusters provide scale without heavy texture files.
  for(let k=0;k<3;k++){const gx=x+size*randHash(xx,yy,k+81),gy=y+size*randHash(xx,yy,k+91);ctx.strokeStyle=k%2?'#a4af742f':'#2f5a362c';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(gx,gy+4*scale);ctx.lineTo(gx-2*scale,gy);ctx.lineTo(gx+1*scale,gy-2*scale);ctx.stroke()}
 }
 // The starting clearing and a dirt trail make the game world easier to navigate.
 const trailX=px(335),trailW=73*scale;ctx.fillStyle='#ad9a6b6b';ctx.fillRect(trailX-trailW/2,0,trailW,h);
 for(let y=-17;y<17;y++){const x=px(337+(randHash(y,72)-.5)*39),sy=py(y*140);if(sy<-30||sy>h+30)continue;ellipse(x,sy,11*scale,5*scale,'#796d4c32')}
 const clearingX=px(0),clearingY=py(0);ellipse(clearingX,clearingY,168*scale,145*scale,'#b5a06d25');
}
function visible(x,y,pad=100){const sx=px(x),sy=py(y);return sx>-pad&&sy>-pad&&sx<viewport.w+pad&&sy<viewport.h+pad}
function drawTree(n){const x=px(n.x),y=py(n.y),s=n.size*viewport.scale;ellipse(x+6*viewport.scale,y+s*.75,s*.85,s*.39,'#1b372447');ellipse(x,y+s*.25,s*.35,s*.35,'#614b32');const vary=(n.variant%4);ellipse(x-s*.36,y-s*.13,s*.65,s*.59,['#355d37','#3e643d','#3a6239','#43653c'][vary]);ellipse(x+s*.31,y-s*.25,s*.75,s*.67,['#487548','#3a6a3f','#426c3f','#32613b'][vary]);ellipse(x-s*.12,y-s*.48,s*.84,s*.72,['#4f8350','#518345','#3b7749','#4a7950'][vary]);ellipse(x-s*.29,y-s*.62,s*.39,s*.24,'#8aaa5a61');ellipse(x+s*.18,y-s*.65,s*.35,s*.19,'#a0bc7354');for(let i=0;i<4;i++){const a=randHash(n.variant,i)*TAU;ellipse(x+Math.cos(a)*s*.52,y-s*.25+Math.sin(a)*s*.48,s*.13,s*.12,'#1b4d325e')}}
function drawRock(n){const x=px(n.x),y=py(n.y),s=n.size*viewport.scale;ellipse(x+3,y+s*.50,s*1.1,s*.48,'#1f362b56');polygon([[x-s*.93,y+s*.17],[x-s*.55,y-s*.66],[x+s*.25,y-s*.85],[x+s*.94,y-s*.25],[x+s*.82,y+s*.47],[x-s*.15,y+s*.70]],'#75857d','#48584f');polygon([[x-s*.93,y+s*.17],[x-s*.55,y-s*.66],[x+s*.05,y-s*.14],[x-s*.15,y+s*.70]],'#9ba79d');polygon([[x+s*.05,y-s*.14],[x+s*.25,y-s*.85],[x+s*.94,y-s*.25],[x+s*.82,y+s*.47]],'#5a6d64');ctx.strokeStyle='#c3c7b43d';ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(x-s*.38,y-s*.40);ctx.lineTo(x+s*.05,y-s*.15);ctx.stroke()}
function drawBush(n){const x=px(n.x),y=py(n.y),s=n.size*viewport.scale;ellipse(x+2,y+s*.44,s*1.07,s*.47,'#203e2e42');ellipse(x-s*.36,y,s*.61,s*.54,'#356945');ellipse(x+s*.29,y-s*.18,s*.62,s*.60,'#497b49');ellipse(x,y-s*.42,s*.62,s*.56,'#548d4b');for(let k=0;k<5;k++){const a=k*TAU/5;ellipse(x+Math.cos(a)*s*.46,y-s*.2+Math.sin(a)*s*.4,s*.12,s*.13,'#8aad58')};}
function drawCrate(n){const x=px(n.x),y=py(n.y),s=n.size*viewport.scale;ellipse(x+3,y+s*.75,s*.89,s*.45,'#28372a5b');polygon([[x-s*.83,y-s*.42],[x+s*.4,y-s*.58],[x+s*.93,y-s*.22],[x-s*.28,y-s*.05]],'#c5a574','#6a5134');polygon([[x-s*.83,y-s*.42],[x-s*.28,y-s*.05],[x-s*.28,y+s*.63],[x-s*.83,y+s*.29]],'#8b623d');polygon([[x-s*.28,y-s*.05],[x+s*.93,y-s*.22],[x+s*.93,y+s*.41],[x-s*.28,y+s*.63]],'#9e7648');ctx.strokeStyle='#dbbc80aa';ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(x+s*.02,y-s*.42);ctx.lineTo(x+s*.02,y+s*.52);ctx.moveTo(x-s*.84,y+s*.04);ctx.lineTo(x-s*.28,y+s*.39);ctx.moveTo(x-s*.25,y+s*.32);ctx.lineTo(x+s*.91,y+s*.13);ctx.stroke()}
function drawWall(b){const x=px(b.x),y=py(b.y),s=viewport.scale;ellipse(x,y+18*s,36*s,14*s,'#111c1647');roundRect(x-29*s,y-23*s,58*s,43*s,5*s,'#5c4d33','#302d22');for(let i=0;i<4;i++){roundRect(x-27*s,y-20*s+i*10*s,54*s,8*s,1,'#86623c','#3e3829');ctx.strokeStyle='#d1ac6b48';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(x-20*s,y-17*s+i*10*s);ctx.lineTo(x+15*s,y-17*s+i*10*s);ctx.stroke()}roundRect(x-26*s,y-19*s,6*s,35*s,1,'#493b2a');roundRect(x+19*s,y-19*s,6*s,35*s,1,'#493b2a')}
function drawFloor(b){const x=px(b.x),y=py(b.y),s=viewport.scale;roundRect(x-27*s,y-27*s,54*s,54*s,2,'#806946','#634c36');for(let i=0;i<4;i++){ctx.strokeStyle='#bea07288';ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(x-25*s,y+(-17+i*12)*s);ctx.lineTo(x+25*s,y+(-17+i*12)*s);ctx.stroke()}}
function drawFire(b){const x=px(b.x),y=py(b.y),s=viewport.scale;ellipse(x+5*s,y+20*s,35*s,17*s,'#27362775');ellipse(x,y+10*s,25*s,15*s,'#786f5c');for(let i=0;i<7;i++){const a=i*TAU/7;ellipse(x+Math.cos(a)*20*s,y+10*s+Math.sin(a)*10*s,6*s,4*s,'#9d9b84',a)}for(let i=0;i<3;i++){const a=i*TAU/3;ctx.save();ctx.translate(x,y+10*s);ctx.rotate(a);roundRect(-18*s,-3*s,36*s,6*s,2*s,'#674930','#3d3025');ctx.restore()}const f=Math.sin(state.elapsed*8+b.x)*4*s;polygon([[x-10*s,y+3*s],[x-3*s,y-15*s+f],[x+2*s,y-25*s-f],[x+12*s,y+5*s]],'#ef8b3c');polygon([[x-4*s,y+3*s],[x+2*s,y-15*s+f*.5],[x+7*s,y+4*s]],'#f9d471');}
function drawStorage(b){drawCrate({...b,size:22,variant:5})}
function drawBuilding(b){if(b.kind==='wall')drawWall(b);else if(b.kind==='floor')drawFloor(b);else if(b.kind==='storage')drawStorage(b);else drawFire(b)}
function drawHumanoid(x,y,dir,walk,infected=false,zombie=null){const s=viewport.scale,xx=px(x),yy=py(y);const moving=walk>0;ctx.save();ctx.translate(xx,yy);ctx.rotate(dir);const bob=moving?Math.sin(walk*9)*1.5*s:Math.sin(state.elapsed*2.2)*.65*s;const stride=moving?Math.sin(walk*9)*5*s:0;
 ellipse(4*s,12*s,18*s,8*s,'#172c1b72');
 // Outfit/leg layers below the torso make gear visible from overhead.
 const legs=infected?'#423e35':state.equipment.legs==='cargo'?'#495342':'#bda084';
 roundRect(-10*s,2*s+stride,8*s,17*s,3*s,legs);roundRect(2*s,2*s-stride,8*s,17*s,3*s,legs);
 const feet=infected?'#343b2d':state.equipment.feet==='boots'?'#493727':'#866547';
 ellipse(-6*s,18*s+stride,5*s,4*s,feet);ellipse(6*s,18*s-stride,5*s,4*s,feet);
 if(!infected && state.equipment.back==='backpack'){roundRect(-16*s,-12*s,32*s,27*s,8*s,'#685f3d','#403e30');roundRect(-11*s,-9*s,22*s,19*s,5*s,'#817348');roundRect(-7*s,-15*s,14*s,8*s,4*s,'#434b35')}
 const baseSkin=infected?'#91a17d':'#c08a63';
 const top=infected?'#51574a':state.equipment.chest==='hoodie'?'#4d6554':state.equipment.chest==='shirt'?'#a09d88':baseSkin;
 ctx.save();ctx.translate(0,bob);
 // T-shirt silhouette, arms and hands.
 ellipse(-13*s,-4*s,7*s,11*s,infected?'#9aa681':top,.20);ellipse(13*s,-4*s,7*s,11*s,infected?'#9aa681':top,-.20);
 ellipse(-17*s,5*s,4.3*s,5.4*s,baseSkin);ellipse(17*s,5*s,4.3*s,5.4*s,baseSkin);
 roundRect(-12*s,-16*s,24*s,26*s,8*s,top);
 if(!infected && !state.equipment.chest){ctx.strokeStyle='#825b49';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(0,-8*s);ctx.lineTo(0,8*s);ctx.stroke()}
 if(!infected && state.equipment.chest==='hoodie'){roundRect(-10*s,-15*s,20*s,6*s,2*s,'#6d7e62')}
 if(!infected && state.equipment.chest==='shirt'){ctx.strokeStyle='#626d61';ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(-9*s,7*s);ctx.lineTo(9*s,7*s);ctx.stroke()}
 // Head and hair, visually characteristic of the starting survivor.
 ellipse(0,-17*s,11*s,11*s,infected?'#8c9f76':'#d1a07a');
 if(infected){ellipse(-4*s,-20*s,2.4*s,2*s,'#c95450');ellipse(4*s,-20*s,2.4*s,2*s,'#d15b55');ellipse(0,-13*s,5*s,2*s,'#53694e');polygon([[-11*s,-24*s],[-7*s,-31*s],[4*s,-29*s],[11*s,-24*s]],'#4b4938')}
 else{ellipse(0,-24*s,11*s,6*s,'#423226');polygon([[-10*s,-25*s],[-7*s,-33*s],[-3*s,-30*s],[0,-34*s],[6*s,-31*s],[9*s,-29*s],[10*s,-25*s]],'#49372b');ellipse(-4*s,-16*s,1.6*s,1.2*s,'#493525');ellipse(4*s,-16*s,1.6*s,1.2*s,'#493525');ellipse(0,-12*s,4*s,2*s,'#67442c')}
 if(!infected){let hand=state.equipment.hand;const p=state.player;const swing=(p.attacking>0?Math.sin((.36-p.attacking)/.36*Math.PI)*.85:0);ctx.save();ctx.translate(16*s,1*s);ctx.rotate(swing);
 if(hand==='axe'){ctx.strokeStyle='#8b6945';ctx.lineWidth=4*s;ctx.beginPath();ctx.moveTo(0,8*s);ctx.lineTo(4*s,-23*s);ctx.stroke();polygon([[0,-22*s],[15*s,-26*s],[18*s,-17*s],[2*s,-15*s]],'#b9c0af','#536354')}
 if(hand==='pickaxe'){ctx.strokeStyle='#997952';ctx.lineWidth=3.3*s;ctx.beginPath();ctx.moveTo(0,8*s);ctx.lineTo(4*s,-25*s);ctx.stroke();polygon([[-9*s,-23*s],[3*s,-30*s],[15*s,-24*s],[4*s,-21*s]],'#b4c1b5')}
 if(hand==='spear'){ctx.strokeStyle='#8e6b40';ctx.lineWidth=3.2*s;ctx.beginPath();ctx.moveTo(0,10*s);ctx.lineTo(1*s,-38*s);ctx.stroke();polygon([[-6*s,-37*s],[1*s,-48*s],[7*s,-37*s]],'#b9c4b4')}
 if(hand==='torch'){ctx.strokeStyle='#936c46';ctx.lineWidth=5*s;ctx.beginPath();ctx.moveTo(0,7*s);ctx.lineTo(1*s,-21*s);ctx.stroke();ellipse(1*s,-23*s,6*s,9*s,'#ffac4c');ellipse(1*s,-25*s,3*s,5*s,'#ffe29a')}
 ctx.restore();}
 ctx.restore();ctx.restore();
 if(infected&&zombie&&zombie.stagger>0)ellipse(xx,yy-12*s,15*s,25*s,'#ff525126')
}
function drawZombie(z){if(z.hp<=0)return;drawHumanoid(z.x,z.y,z.dir,z.walk,true,z)}
function drawPlayer(){drawHumanoid(state.player.x,state.player.y,state.player.dir,state.player.anim,false);if(state.player.hurt>0&&Math.floor(state.elapsed*14)%2===0){ellipse(px(state.player.x),py(state.player.y)-12,20*viewport.scale,29*viewport.scale,'#ff8b7540')}}
function drawEffect(e){const t=e.t/e.life,s=viewport.scale,x=px(e.x),y=py(e.y);ctx.save();ctx.globalAlpha=clamp(1-t,0,1);if(e.kind==='text'){ctx.font=`900 ${13*s}px system-ui`;ctx.textAlign='center';ctx.lineWidth=3;ctx.strokeStyle='#12231d';ctx.strokeText(e.text,x,y-34*t*s);ctx.fillStyle=e.color;ctx.fillText(e.text,x,y-34*t*s)}
 else if(e.kind==='slash'){ctx.translate(x,y);ctx.rotate(e.angle);ctx.strokeStyle=e.color;ctx.lineWidth=4*s;ctx.lineCap='round';ctx.beginPath();ctx.arc(0,0,(22+t*23)*s,-.7,1.3);ctx.stroke()}
 else if(e.kind==='burst'){for(let k=0;k<9;k++){const a=k*TAU/9+t;ellipse(x+Math.cos(a)*42*t*s,y+Math.sin(a)*30*t*s,4*s*(1-t),4*s*(1-t),e.color)}}ctx.restore()}
function drawTargetMarkers(){let n=nearbyNode(85),z=nearbyZombie(65);if(n&&!paused){const x=px(n.x),y=py(n.y),r=(n.size+9)*viewport.scale;ctx.strokeStyle='#fff1b2bb';ctx.lineWidth=2;ctx.setLineDash([6,5]);ctx.beginPath();ctx.ellipse(x,y,r,r*.78,0,0,TAU);ctx.stroke();ctx.setLineDash([])}else if(z&&!paused){ctx.strokeStyle='#e79f8caf';ctx.lineWidth=2;ctx.beginPath();ctx.arc(px(z.x),py(z.y),29*viewport.scale,0,TAU);ctx.stroke()}}
function drawNight(){let dayFrac=(state.elapsed%600)/600;const hour=(6+dayFrac*24)%24;let darkness=hour>=19?Math.min(.55,(hour-19)*.1+.2):hour<5?.56:hour<7?Math.max(0,.4-(hour-5)*.2):0;if(darkness<.02)return;ctx.fillStyle=`rgba(9,24,34,${darkness})`;ctx.fillRect(0,0,viewport.w,viewport.h);for(const b of buildings){if(b.kind==='campfire'&&visible(b.x,b.y,140)){let x=px(b.x),y=py(b.y);let g=ctx.createRadialGradient(x,y,8,x,y,195*viewport.scale);g.addColorStop(0,'#ffbb6d35');g.addColorStop(1,'#ffbb6d00');ctx.fillStyle=g;ctx.beginPath();ctx.arc(x,y,195*viewport.scale,0,TAU);ctx.fill()}}if(state.equipment.hand==='torch'){let x=px(state.player.x),y=py(state.player.y);let g=ctx.createRadialGradient(x,y,4,x,y,150*viewport.scale);g.addColorStop(0,'#ffd58144');g.addColorStop(1,'#ffd58100');ctx.fillStyle=g;ctx.beginPath();ctx.arc(x,y,150*viewport.scale,0,TAU);ctx.fill()}}
function render(){const {w,h}=viewport;ctx.setTransform(viewport.dpr,0,0,viewport.dpr,0,0);ctx.save();if(screenShake>.1)ctx.translate((Math.random()-.5)*screenShake,(Math.random()-.5)*screenShake);drawGround();const visibles=[];for(const n of nodes){if(!nodeActive(n)||!visible(n.x,n.y,105))continue;visibles.push({y:n.y,kind:'node',v:n})}for(const b of buildings)if(visible(b.x,b.y,100))visibles.push({y:b.y,kind:'building',v:b});for(const z of zombies)if(z.hp>0&&visible(z.x,z.y,100))visibles.push({y:z.y,kind:'zombie',v:z});visibles.push({y:state.player.y,kind:'player'});visibles.sort((a,b)=>a.y-b.y);for(const o of visibles){if(o.kind==='node'){if(o.v.kind==='tree')drawTree(o.v);else if(o.v.kind==='rock')drawRock(o.v);else if(o.v.kind==='bush')drawBush(o.v);else drawCrate(o.v)}else if(o.kind==='building')drawBuilding(o.v);else if(o.kind==='zombie')drawZombie(o.v);else drawPlayer()}
 for(const e of effects)if(visible(e.x,e.y,100))drawEffect(e);
 drawTargetMarkers();drawNight();if(hitFlash>.02){ctx.fillStyle=`rgba(163,18,27,${hitFlash*.16})`;ctx.fillRect(0,0,w,h)}ctx.restore()}

function collides(x,y){if(Math.abs(x)>WORLD_LIMIT||Math.abs(y)>WORLD_LIMIT)return true;for(const n of nodes)if(nodeActive(n)&&['tree','rock'].includes(n.kind)&&distance(x,y,n.x,n.y)<n.size*.67+14)return true;for(const b of buildings)if(b.kind==='wall'&&distance(x,y,b.x,b.y)<36)return true;return false}
function movementVector(){let dx=joy.x,dy=joy.y;if(keys.has('w')||keys.has('arrowup'))dy-=1;if(keys.has('s')||keys.has('arrowdown'))dy+=1;if(keys.has('a')||keys.has('arrowleft'))dx-=1;if(keys.has('d')||keys.has('arrowright'))dx+=1;let magnitude=Math.hypot(dx,dy);return magnitude>1?{dx:dx/magnitude,dy:dy/magnitude}: {dx,dy}}
function update(dt){if(paused||gameOver)return;const p=state.player;state.elapsed+=dt;autosaveClock+=dt;updateClock+=dt;enemySpawnClock+=dt;
 p.attackCooldown=Math.max(0,p.attackCooldown-dt);p.attacking=Math.max(0,p.attacking-dt);p.hurt=Math.max(0,p.hurt-dt);hitFlash=Math.max(0,hitFlash-dt);screenShake=Math.max(0,screenShake-dt*26);
 state.hunger=Math.max(0,state.hunger-dt*.029);state.thirst=Math.max(0,state.thirst-dt*.04);state.stamina=Math.min(100,state.stamina+dt*9);
 if(state.hunger<=0||state.thirst<=0)state.hp=Math.max(0,state.hp-dt*2);if(state.hp<=0){die();return}
 const {dx,dy}=movementVector();const speed=state.stamina>1?141:91;const moving=Math.hypot(dx,dy)>.06;
 if(moving){const vx=dx*speed*dt,vy=dy*speed*dt;if(!collides(p.x+vx,p.y))p.x+=vx;if(!collides(p.x,p.y+vy))p.y+=vy;p.dir=Math.atan2(dx,-dy);p.anim+=dt*(state.stamina>1?2.0:1.2);state.stamina=Math.max(0,state.stamina-dt*.67)}else p.anim=0;
 camera.x+=(p.x-camera.x)*Math.min(1,dt*7);camera.y+=(p.y-camera.y)*Math.min(1,dt*7);
 for(const n of nodes)if(n.regenAt>0&&n.regenAt<=state.elapsed){n.hp=n.maxhp;n.regenAt=0}
 for(const z of zombies){if(z.hp<=0){if(z.deadUntil<=state.elapsed){z.hp=3;z.x=z.spawnX;z.y=z.spawnY;z.attackCooldown=.8}continue}z.attackCooldown=Math.max(0,z.attackCooldown-dt);z.stagger=Math.max(0,z.stagger-dt);const d=distance(z.x,z.y,p.x,p.y);if(d<310&&z.stagger<=0){const vx=(p.x-z.x)/(d||1),vy=(p.y-z.y)/(d||1);z.dir=Math.atan2(vx,-vy);if(d>29){const zs=44*dt;z.x+=vx*zs;z.y+=vy*zs;z.walk+=dt*1.6}else if(z.attackCooldown<=0){hurtPlayer(10);z.attackCooldown=1.65;effects.push({kind:'slash',x:p.x,y:p.y-12,t:0,life:.32,angle:z.dir,color:'#fd9b86'})}}else if(d<440){z.walk+=dt*.1}}
 // Timed nearby infection pressure, capped for mobile performance.
 if(enemySpawnClock>42){enemySpawnClock=0;if(zombies.filter(z=>z.hp>0&&distance(z.x,z.y,p.x,p.y)<650).length<5&&zombies.length<80){const a=Math.random()*TAU,r=480+Math.random()*160;addZombie(clamp(p.x+Math.cos(a)*r,-WORLD_LIMIT,WORLD_LIMIT),clamp(p.y+Math.sin(a)*r,-WORLD_LIMIT,WORLD_LIMIT));}}
 for(let i=effects.length-1;i>=0;i--){effects[i].t+=dt;if(effects[i].t>effects[i].life)effects.splice(i,1)}
 if(autosaveClock>=12){autosaveClock=0;saveGame()}
 if(updateClock>.12){updateClock=0;status();updatePrompt()}
}
function updatePrompt(){const n=nearbyNode(87),z=nearbyZombie(69);const content=n?n.kind==='tree'?'✦ GATHER · CHOP TREE':n.kind==='rock'?'✦ GATHER · MINE ROCK':n.kind==='bush'?'✦ GATHER · PLANT FIBER':'✦ GATHER · LOOT CRATE':z?'⚔ ATTACK · INFECTED NEARBY':'MOVE · GATHER · CRAFT · BUILD';$('action-prompt').textContent=content}
let lastFrame=performance.now();function tick(t){let dt=Math.min((t-lastFrame)/1000,.055);lastFrame=t;update(dt);render();requestAnimationFrame(tick)}

// Touch and keyboard controls.
const stick=$('joystick'),knob=$('joystick-inner');
function pointerJoy(e){const b=stick.getBoundingClientRect(),centerX=b.left+b.width/2,centerY=b.top+b.height/2,radius=b.width*.31;let x=e.clientX-centerX,y=e.clientY-centerY;const len=Math.hypot(x,y);if(len>radius){x*=radius/len;y*=radius/len}joy.x=clamp(x/radius,-1,1);joy.y=clamp(y/radius,-1,1);knob.style.transform=`translate(${x}px,${y}px)`}
function resetJoy(){joy.pointer=null;joy.x=0;joy.y=0;knob.style.transform='translate(0px,0px)'}
stick.addEventListener('pointerdown',e=>{e.preventDefault();joy.pointer=e.pointerId;stick.setPointerCapture(e.pointerId);pointerJoy(e)});
stick.addEventListener('pointermove',e=>{if(e.pointerId===joy.pointer){e.preventDefault();pointerJoy(e)}});
for(const name of ['pointerup','pointercancel','lostpointercapture'])stick.addEventListener(name,e=>{if(e.pointerId===joy.pointer)resetJoy()});
$('interact-btn').addEventListener('pointerdown',e=>{e.preventDefault();gather()});$('attack-btn').addEventListener('pointerdown',e=>{e.preventDefault();attack()});
for(const el of document.querySelectorAll('[data-open]'))el.addEventListener('click',()=>openModal(el.dataset.open));
for(const el of document.querySelectorAll('[data-quick]'))el.addEventListener('click',()=>useQuick(Number(el.dataset.quick)));
$('pause-btn').addEventListener('click',()=>openModal('settings'));
$('close-modal').addEventListener('click',closeModal);
$('modal-shell').addEventListener('pointerdown',e=>{if(e.target===$('modal-shell'))closeModal()});
$('modal-content').addEventListener('click',handleModalAction);
for(const tab of document.querySelectorAll('[data-tab]'))tab.addEventListener('click',()=>{modal=tab.dataset.tab;renderModal()});
$('respawn-btn').addEventListener('click',respawn);
$('dismiss-onboarding').addEventListener('click',()=>{$('onboarding').classList.add('hidden');try{localStorage.setItem('glitch-survival-2d-tip','1')}catch(e){}});
window.addEventListener('keydown',e=>{const k=e.key.toLowerCase();if(['arrowup','arrowdown','arrowleft','arrowright',' '].includes(k))e.preventDefault();if(e.repeat&&['e',' ','i','c','b','g','escape'].includes(k))return;if(k==='escape'){if(modal)closeModal();else openModal('settings');return}if(modal){if(k==='i'||k==='g'||k==='b'||k==='c')closeModal();return}keys.add(k);if(k==='e'||k==='f')gather();else if(k===' ')attack();else if(k==='i')openModal('inventory');else if(k==='c')openModal('craft');else if(k==='b')openModal('build');else if(k==='g')openModal('gear');else if(/^[1-5]$/.test(k))useQuick(Number(k)-1)});
window.addEventListener('keyup',e=>keys.delete(e.key.toLowerCase()));
window.addEventListener('blur',()=>{keys.clear();resetJoy();saveGame()});
window.addEventListener('pagehide',()=>saveGame());
window.addEventListener('resize',resize);
window.addEventListener('orientationchange',()=>{resize();setTimeout(resize,250)});
if(window.visualViewport)window.visualViewport.addEventListener('resize',resize);

// Start the new 2D world. Old 3D save keys are intentionally untouched.
createWorld();
const resumed=loadGame();if(!resumed){camera.x=state.player.x;camera.y=state.player.y}
resize();status();updatePrompt();
if(resumed||(()=>{try{return localStorage.getItem('glitch-survival-2d-tip')==='1'}catch(e){return false}})())$('onboarding').classList.add('hidden');
if(resumed)showToast('Welcome back to your 2D survivor camp!');else showToast('NEW WORLD · Day 1 begins. Gather resources and survive!',3700);
requestAnimationFrame(tick);
// Small read-only diagnostics for automated browser tests.
window.__GLITCH_DIAGNOSTICS__={getSnapshot:()=>({player:{x:state.player.x,y:state.player.y},stats:{hp:state.hp,hunger:state.hunger,thirst:state.thirst},inventory:{...state.inventory},equipment:{...state.equipment},nodes:nodes.length,zombies:zombies.length,buildings:buildings.length,paused,modal,elapsed:state.elapsed}),getMove:movementVector};
})();


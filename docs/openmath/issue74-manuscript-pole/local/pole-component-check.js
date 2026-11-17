// Exact finite check of the actual JavaScript pole component, not a Diophantine proof.
const {PolynomialLibrary}=require('../../../../construction/rational-polynomial-library.js');
const {addCore}=require('../../../../construction/multiplication-certificate.js');
const lib=new PolynomialLibrary();addCore(lib);const t=lib.templates[lib.id('pole')];
function evaluate(x){const v=[];for(const n of t.nodes){
  if(n.op==='const')v.push(BigInt(n.args[0]));
  else if(n.op==='var')v.push(x[n.args[0]]);
  else if(n.op==='add')v.push(v[n.args[0]]+v[n.args[1]]);
  else if(n.op==='mul')v.push(v[n.args[0]]*v[n.args[1]]);
  else throw Error('Unexpected operation '+n.op);
}return v[t.root];}
const x=[2n,0n,0n,0n,0n,0n,0n,1n,1n,0n,0n,0n];
if(t.witnessCount!==11 || evaluate(x)!==29002n**2n)throw Error('Manuscript pole mismatch');
if(evaluate(x)===1226n**2n)throw Error('Wrong-route control was accepted');
x[0]=0n;if(evaluate(x)!==0n)throw Error('B=0 boundary changed');
console.log(JSON.stringify({scope:'exact finite component check',witnesses:11,
  manuscript_value:'841116004',route_k_value:'1503076',zero_input:'PASS',
  arithmetic_theorem_proved:false},null,2));

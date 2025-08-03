function solve(formula) {
  // VALIDATE INPUT AND DETERMINE CNF PARAMETERS
  if(!Array.isArray(formula)) { throw new TypeError("Invalid formula"); }

  const m = formula.length;
  let n = 0;
  let p = 0;
  for(let i = 0; i < m; i++) {
    const clause = formula[i];
    if(!Array.isArray(clause)) { throw new TypeError("Invalid clause"); }

    const l = clause.length;
    if(l < 1) { return []; } // UNSAT

    p += l;

    for(let j = 0; j < l; j++) {
      const literal = clause[j];
      if(!Number.isInteger(literal)) { throw new TypeError("Invalid literal"); }
 
      const variable = Math.abs(literal);
      if(!(variable >= 1)) { throw new RangeError("Invalid variable"); }
      if(!(variable < 2147483649)) { throw new RangeError("Too many variables"); }

      if(variable > n) { n = variable; }
    }
  }

  // ALLOCATE AND INITIALIZE DATA STRUCTURES
  // FIXME: Allocate one big ArrayBuffer and slice these out of it!
  const literals = new Uint32Array(p);
  const start = new Uint32Array(m + 1);
  const watch = new Uint32Array(n * 2).fill(m);
  const next = new Uint32Array(m).fill(m);
  const move = new Uint32Array(n);

  for(let i = 0, k = 0; i < m; i++) {
    start[i] = k;

    const clause = formula[i];
    const l = clause.length;
    for(let j = 0; j < l; j++, k++) {
      const literal = clause[j];
      literals[k] = (Math.abs(literal) - 1) * 2 + (literal >>> 31);
    }
  }

  start[m] = p;

  for(let i = m; i--; ) {
    const literal = formula[i][0];
    const j = (Math.abs(literal) - 1) * 2 + (literal >>> 31);
    next[i] = watch[j];
    watch[j] = i;
  }

  console.log("literals = (%s)", literals.join(" "));
  console.log("start = (%s)", start.join(" "));
  console.log("watch = (%s)", watch.join(" "));
  console.log("next = (%s)", next.join(" "));
}

solve([ 
  [ 1,  2, -3],
  [ 2,  3, -4], 
  [ 3,  4,  1],
  [ 4, -1,  2],
  [-1, -2,  3],  
  [-2, -3,  4],
  [-3, -4, -1],
]);

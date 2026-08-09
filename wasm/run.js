// Run a compiled λE module and print its result.
//
//     node wasm/run.js program.wasm
//
// Values are self-describing cells in linear memory, so this walks the heap
// from the pointer `main` returns and renders it in exactly the format of
// lib/core/pretty.ml — which is what lets the compiled output be diffed
// against the OCaml interpreter.

const fs = require('fs');

const TAG = {
  INT: 0, BOOL: 1, STR: 2, UNIT: 3, MRG: 4,
  LREC: 5, CLOS: 6, FCLOS: 7, INL: 8, INR: 9, FOLD: 10,
};

// Mirrors OCaml's %S: escapes the four named controls, quotes and backslash,
// and falls back to three-digit *decimal* escapes.
function ocamlStringLit(bytes) {
  let out = '"';
  for (const c of bytes) {
    if (c === 0x22) out += '\\"';
    else if (c === 0x5c) out += '\\\\';
    else if (c === 0x0a) out += '\\n';
    else if (c === 0x09) out += '\\t';
    else if (c === 0x0d) out += '\\r';
    else if (c === 0x08) out += '\\b';
    else if (c < 32 || c >= 127) out += '\\' + String(c).padStart(3, '0');
    else out += String.fromCharCode(c);
  }
  return out + '"';
}

function main() {
  const path = process.argv[2];
  if (!path) {
    console.error('usage: node run.js program.wasm');
    process.exit(64);
  }
  const bytes = fs.readFileSync(path);

  let instance;
  try {
    const mod = new WebAssembly.Module(bytes);
    instance = new WebAssembly.Instance(mod, {});
  } catch (e) {
    console.log('invalid: ' + e.message);
    process.exit(2);
  }

  let result;
  try {
    result = instance.exports.main();
  } catch (e) {
    // A trap is how the compiled program reports what the interpreter reports
    // with Failure — division by zero, most of all.
    console.log('trap: ' + e.message);
    process.exit(3);
  }

  // Read the buffer only now: allocation may have grown the memory, which
  // detaches any view taken earlier.
  const buffer = instance.exports.memory.buffer;
  const dv = new DataView(buffer);
  const u8 = new Uint8Array(buffer);
  const i32 = (p) => dv.getInt32(p, true);

  const labelsAddr = instance.exports.labels.value;
  const labelCount = i32(labelsAddr);
  const labels = [];
  for (let i = 0; i < labelCount; i++) {
    const off = i32(labelsAddr + 4 + i * 8);
    const len = i32(labelsAddr + 8 + i * 8);
    labels.push(Buffer.from(u8.subarray(off, off + len)).toString('latin1'));
  }

  // A merge whose whole spine is labelled prints as a record, matching the
  // rule in pretty.ml.
  function recordFields(p) {
    switch (i32(p)) {
      case TAG.LREC:
        return [[labels[i32(p + 4)], i32(p + 8)]];
      case TAG.MRG: {
        const l = recordFields(i32(p + 4));
        if (!l) return null;
        const r = recordFields(i32(p + 8));
        return r ? l.concat(r) : null;
      }
      default:
        return null;
    }
  }

  function render(p) {
    const fields = recordFields(p);
    if (fields && fields.length > 0) {
      return '{ ' + fields.map(([l, v]) => `${l} = ${render(v)}`).join('; ') + ' }';
    }
    const a = i32(p + 4);
    const b = i32(p + 8);
    switch (i32(p)) {
      case TAG.INT: return String(a);
      case TAG.BOOL: return a ? 'true' : 'false';
      case TAG.STR: return ocamlStringLit(u8.subarray(a, a + b));
      case TAG.UNIT: return '()';
      case TAG.MRG: return `(${render(a)} ,, ${render(b)})`;
      case TAG.LREC: return `{ ${labels[a]} = ${render(b)} }`;
      case TAG.CLOS: return '<fun>';
      case TAG.FCLOS: return '<rec fun>';
      case TAG.INL: return `inl ${render(a)}`;
      case TAG.INR: return `inr ${render(a)}`;
      case TAG.FOLD: return `fold ${render(a)}`;
      default: throw new Error(`unknown tag ${i32(p)} at ${p}`);
    }
  }

  console.log(render(result));
}

main();

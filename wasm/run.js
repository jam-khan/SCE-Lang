// Run a compiled λE module and print its result.
//
//     node wasm/run.js program.wasm
//
// Values are GC structs, which JavaScript cannot look inside — so the module
// exports accessor functions (tag, pairA, lrecVal, ...) and this walks the
// result through them, rendering in exactly the format of lib/core/pretty.ml.
// That is what lets the compiled output be diffed against the OCaml
// interpreter. The label id -> name table travels in the "sce.labels" custom
// section rather than in the module's state.

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

// count:u32le, then per label: length:u32le + bytes
function parseLabels(mod) {
  const sections = WebAssembly.Module.customSections(mod, 'sce.labels');
  if (sections.length === 0) return [];
  const dv = new DataView(sections[0]);
  const u8 = new Uint8Array(sections[0]);
  const labels = [];
  let p = 4;
  const count = dv.getUint32(0, true);
  for (let i = 0; i < count; i++) {
    const len = dv.getUint32(p, true);
    labels.push(Buffer.from(u8.subarray(p + 4, p + 4 + len)).toString('latin1'));
    p += 4 + len;
  }
  return labels;
}

function main() {
  const path = process.argv[2];
  if (!path) {
    console.error('usage: node run.js program.wasm');
    process.exit(64);
  }
  const bytes = fs.readFileSync(path);

  let mod, x;
  try {
    mod = new WebAssembly.Module(bytes);
    x = new WebAssembly.Instance(mod, {}).exports;
  } catch (e) {
    console.log('invalid: ' + e.message);
    process.exit(2);
  }
  const labels = parseLabels(mod);

  let result;
  try {
    result = x.main();
  } catch (e) {
    // A trap is how the compiled program reports what the interpreter reports
    // with Failure — division by zero, most of all.
    console.log('trap: ' + e.message);
    process.exit(3);
  }

  function str(v) {
    const len = x.strLen(v);
    const out = new Uint8Array(len);
    for (let i = 0; i < len; i++) out[i] = x.strByte(v, i);
    return out;
  }

  // A merge whose whole spine is labelled prints as a record, matching the
  // rule in pretty.ml.
  function recordFields(v) {
    switch (x.tag(v)) {
      case TAG.LREC:
        return [[labels[x.lrecLabel(v)], x.lrecVal(v)]];
      case TAG.MRG: {
        const l = recordFields(x.pairA(v));
        if (!l) return null;
        const r = recordFields(x.pairB(v));
        return r ? l.concat(r) : null;
      }
      default:
        return null;
    }
  }

  function render(v) {
    const fields = recordFields(v);
    if (fields && fields.length > 0) {
      return '{ ' + fields.map(([l, w]) => `${l} = ${render(w)}`).join('; ') + ' }';
    }
    switch (x.tag(v)) {
      case TAG.INT: return String(x.num(v));
      case TAG.BOOL: return x.num(v) ? 'true' : 'false';
      case TAG.STR: return ocamlStringLit(str(v));
      case TAG.UNIT: return '()';
      case TAG.MRG: return `(${render(x.pairA(v))} ,, ${render(x.pairB(v))})`;
      case TAG.LREC: return `{ ${labels[x.lrecLabel(v)]} = ${render(x.lrecVal(v))} }`;
      case TAG.CLOS: return '<fun>';
      case TAG.FCLOS: return '<rec fun>';
      case TAG.INL: return `inl ${render(x.wrapVal(v))}`;
      case TAG.INR: return `inr ${render(x.wrapVal(v))}`;
      case TAG.FOLD: return `fold ${render(x.wrapVal(v))}`;
      default: throw new Error(`unknown tag ${x.tag(v)}`);
    }
  }

  console.log(render(result));
}

main();

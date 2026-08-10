// Run a compiled λE module and print its result.
//
//     node wasm/run.js program.wasm
//     node wasm/run.js linked.wasm unitA.wasm unitB.wasm ...
//
// The second form instantiates separately compiled unit modules in manifest
// order and wires each one's `main` export into the link module's imports —
// the wasm-level link step. GC type canonicalization is structural, so values
// flow between the instances and the link module's accessors read them all.
//
// Values are GC structs, which JavaScript cannot look inside — so the module
// exports accessor functions (tag, pairA, lrecVal, ...) and this walks the
// result through them, rendering in exactly the format of lib/core/pretty.ml.
// That is what lets the compiled output be diffed against the OCaml
// interpreter. Record labels ride inside the values themselves, so results
// assembled from separately compiled modules render with no shared metadata.

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

// count:u32le, then per name: length:u32le + bytes
function unitManifest(mod) {
  const sections = WebAssembly.Module.customSections(mod, 'sce.units');
  if (sections.length === 0) return null;
  const dv = new DataView(sections[0]);
  const u8 = new Uint8Array(sections[0]);
  const names = [];
  let p = 4;
  for (let i = 0, n = dv.getUint32(0, true); i < n; i++) {
    const len = dv.getUint32(p, true);
    names.push(Buffer.from(u8.subarray(p + 4, p + 4 + len)).toString('latin1'));
    p += 4 + len;
  }
  return names;
}

function main() {
  const path = process.argv[2];
  if (!path) {
    console.error('usage: node run.js program.wasm [unit.wasm ...]');
    process.exit(64);
  }
  const bytes = fs.readFileSync(path);

  let x;
  try {
    const mod = new WebAssembly.Module(bytes);
    const manifest = unitManifest(mod);
    const unitPaths = process.argv.slice(3);
    const importObj = {};
    if (manifest && manifest.length > 0) {
      if (unitPaths.length !== manifest.length) {
        console.error(`this module links ${manifest.length} unit(s): ${manifest.join(', ')}`);
        process.exit(64);
      }
      manifest.forEach((name, k) => {
        const base = require('path').basename(unitPaths[k]).replace(/\.wasm$/, '');
        if (base !== name) {
          console.error(`unit ${k} should be ${name}.wasm, got ${unitPaths[k]}`);
          process.exit(64);
        }
        const inst = new WebAssembly.Instance(
          new WebAssembly.Module(fs.readFileSync(unitPaths[k])), {});
        importObj[`u${k}`] = { main: inst.exports.main };
      });
    }
    x = new WebAssembly.Instance(mod, importObj).exports;
  } catch (e) {
    console.log('invalid: ' + e.message);
    process.exit(2);
  }
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

  function lrecName(v) {
    const len = x.lrecNameLen(v);
    let out = '';
    for (let i = 0; i < len; i++) out += String.fromCharCode(x.lrecNameByte(v, i));
    return out;
  }

  // A merge whose whole spine is labelled prints as a record, matching the
  // rule in pretty.ml.
  function recordFields(v) {
    switch (x.tag(v)) {
      case TAG.LREC:
        return [[lrecName(v), x.lrecVal(v)]];
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
      case TAG.LREC: return `{ ${lrecName(v)} = ${render(x.lrecVal(v))} }`;
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

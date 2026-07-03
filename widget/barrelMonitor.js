/*
 * Infoview panel widget for BARReL import progress (see Barrel/Progress.lean).
 *
 * A global panel widget (registered in Barrel/Progress.lean): polls
 * `Barrel.Progress.get` every 300 ms and stacks one collapsible card per
 * imported machine inside a foldable "Progress" pane (like the infoview's own
 * "Tactic state" / "All Messages"). Each card's bar is layered: a light-blue fill
 * grows with import progress and stays full once imported, then green (proven) +
 * yellow (sorried) segments sit on top — which `prove_obligations_of` keeps filling
 * live as each `next` is discharged. Right of the bar: "<proven> / <total>". Renders
 * nothing until an import reports. Open states (pane and each card) live in React
 * state so they survive the poll re-renders.
 *
 * Plain React.createElement (no JSX, no build step): this file is embedded
 * verbatim into the Lean library with `include_str`.
 *
 * NOTE: editing this file does not retrigger the Lean build by itself — bump the
 * "widget version" note in Barrel/Progress.lean (or `lake build -f Barrel`).
 */
import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';

const BORDER = 'color-mix(in srgb, var(--vscode-foreground, #888) 20%, transparent)';
const CHECK_SVG = '<svg width="9" height="9" viewBox="0 0 16 16" fill="none" stroke="var(--vscode-editor-background, #fff)" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"><polyline points="3 8 6.5 12 13 4"></polyline></svg>';
const CROSS_SVG = '<svg width="8" height="8" viewBox="0 0 16 16" fill="none" stroke="var(--vscode-editor-background, #fff)" stroke-width="2.5" stroke-linecap="round"><line x1="4" y1="4" x2="12" y2="12"></line><line x1="12" y1="4" x2="4" y2="12"></line></svg>';
const CHEVRON_SVG = '<svg width="12" height="12" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="4 6 8 10 12 6"></polyline></svg>';

const GREEN = 'var(--vscode-testing-iconPassed, #3c3)';
const YELLOW = 'var(--vscode-charts-yellow, #d7ba00)';
const RED = 'var(--vscode-testing-iconFailed, #f14c4c)';
const TRACK_GRAY = 'color-mix(in srgb, var(--vscode-foreground, #888) 12%, transparent)';
const IMPORT_BLUE = 'color-mix(in srgb, var(--vscode-progressBar-background, #0078d4) 31%, transparent)';

// Every badge state sits in one fixed square slot, so the row height never changes between
// states and the spinning barrel has room to rotate without its corners being clipped.
const BADGE = { width: 14, height: 14, borderRadius: '50%', flexShrink: 0, boxSizing: 'border-box' };
const SLOT = { display: 'inline-flex', alignItems: 'center', justifyContent: 'center', width: 22, height: 24, flexShrink: 0 };

// BARReL's barrel logo (upright, hooped) used as the "importing" spinner: it turns on its
// vertical axis — the staves scroll sideways past a fixed cylinder-shading gradient (dark
// edges, bright centre) that sells the round surface. Brand golds/browns, not theme-derived.
const BARREL_SVG = '<svg viewBox="0 0 26 34" width="17" height="22" xmlns="http://www.w3.org/2000/svg" role="img" aria-label="importing">'
  + '<defs><clipPath id="barrelClip"><path d="M6.3,6 C1.8,13 1.8,25 6.3,31 Q13,32.3 19.7,31 C24.2,25 24.2,13 19.7,6 Q13,7.3 6.3,6 Z"/></clipPath>'
  + '<linearGradient id="barrelCyl" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#4a2905" stop-opacity=".5"/><stop offset=".2" stop-color="#4a2905" stop-opacity="0"/><stop offset=".4" stop-color="#fff5d0" stop-opacity=".4"/><stop offset=".5" stop-color="#fff5d0" stop-opacity=".12"/><stop offset=".72" stop-color="#4a2905" stop-opacity="0"/><stop offset="1" stop-color="#4a2905" stop-opacity=".5"/></linearGradient></defs>'
  + '<g clip-path="url(#barrelClip)">'
  + '<rect x="0" y="0" width="26" height="34" fill="#e8a62a"/>'
  + '<g>'
  + '<g fill="#c5871a"><rect x="-8" y="0" width="2.8" height="34"/><rect x="-2.4" y="0" width="2.8" height="34"/><rect x="3.2" y="0" width="2.8" height="34"/><rect x="8.8" y="0" width="2.8" height="34"/><rect x="14.4" y="0" width="2.8" height="34"/><rect x="20" y="0" width="2.8" height="34"/><rect x="25.6" y="0" width="2.8" height="34"/></g>'
  + '<g stroke="#7a4a10" stroke-width=".45" opacity=".35"><line x1="-5.2" y1="0" x2="-5.2" y2="34"/><line x1=".4" y1="0" x2=".4" y2="34"/><line x1="6" y1="0" x2="6" y2="34"/><line x1="11.6" y1="0" x2="11.6" y2="34"/><line x1="17.2" y1="0" x2="17.2" y2="34"/><line x1="22.8" y1="0" x2="22.8" y2="34"/><line x1="28.4" y1="0" x2="28.4" y2="34"/></g>'
  + '<animateTransform attributeName="transform" attributeType="XML" type="translate" from="0 0" to="5.6 0" dur="1s" repeatCount="indefinite"/>'
  + '</g>'
  + '<rect x="0" y="0" width="26" height="34" fill="url(#barrelCyl)"/>'
  + '<rect x="0" y="12.2" width="26" height="1.6" fill="#5a3106"/><rect x="0" y="12.2" width="26" height=".45" fill="#9a6a1c"/>'
  + '<rect x="0" y="23.2" width="26" height="1.6" fill="#5a3106"/><rect x="0" y="23.2" width="26" height=".45" fill="#9a6a1c"/>'
  + '</g>'
  + '<path d="M6.3,6 C1.8,13 1.8,25 6.3,31 Q13,32.3 19.7,31 C24.2,25 24.2,13 19.7,6 Q13,7.3 6.3,6 Z" fill="none" stroke="#4a2905" stroke-width="1"/>'
  + '<ellipse cx="13" cy="6" rx="6.6" ry="1.3" fill="#cd951c" stroke="#4a2905" stroke-width=".9"/>'
  + '<ellipse cx="13" cy="6" rx="2.9" ry=".5" fill="#8a5c10" opacity=".5"/>'
  + '</svg>';

function BarrelSpinner() {
  return React.createElement('span', {
    style: { display: 'inline-flex', animation: 'barrel-bob 2s ease-in-out infinite' },
    dangerouslySetInnerHTML: { __html: BARREL_SVG }
  });
}

function StatusIcon({ st }) {
  if (st.importing) {
    return React.createElement(BarrelSpinner, null);
  }
  if (st.total > 0 && st.proven >= st.total) {
    return React.createElement('span', {
      style: { ...BADGE, display: 'inline-flex', background: GREEN, alignItems: 'center', justifyContent: 'center' },
      dangerouslySetInnerHTML: { __html: CHECK_SVG }
    });
  }
  // A thrown error (failing proof, missing/extra `next`s) → red cross.
  if (st.errored) {
    return React.createElement('span', {
      style: { ...BADGE, display: 'inline-flex', background: RED, alignItems: 'center', justifyContent: 'center' },
      dangerouslySetInnerHTML: { __html: CROSS_SVG }
    });
  }
  // Something sorried → yellow dot.
  if (st.sorried > 0) {
    return React.createElement('span', { style: { ...BADGE, display: 'inline-block', background: YELLOW } });
  }
  // Otherwise incomplete but no error yet: gray dot — the goal state may still change.
  return React.createElement('span', { style: { ...BADGE, display: 'inline-block', background: BORDER } });
}

// A layered "double bar": light-gray track underneath; a light-blue layer showing import
// progress (grows po/nbPOs while importing, stays full once done); and, on top, the green
// (proven) + yellow (sorried) proof segments. So after import you see green | remaining blue
// | gray = proven within imported within total.
function ProgressBar({ st }) {
  const outer = { flex: 1, position: 'relative', height: 5, borderRadius: 2, overflow: 'hidden' };
  const track = React.createElement('div', { style: { position: 'absolute', inset: 0, background: TRACK_GRAY } });
  const seg = (left, width, color) => React.createElement('div', { style: { position: 'absolute', left: left + '%', top: 0, height: '100%', width: width + '%', background: color } });
  const importPct = st.importing ? (st.nbPOs > 0 ? Math.min(100, Math.round(100 * st.po / st.nbPOs)) : 0) : 100;
  const total = st.total > 0 ? st.total : 1;
  const g = Math.min(100, Math.round(100 * st.proven / total));
  const y = Math.min(100 - g, Math.round(100 * st.sorried / total));
  return React.createElement('div', { style: outer },
    track,
    seg(0, importPct, IMPORT_BLUE),
    seg(0, g, GREEN),
    seg(g, y, YELLOW));
}

function StatRow({ label, value, divider = true }) {
  return React.createElement('div', { style: { display: 'flex', justifyContent: 'space-between', padding: '7px 2px', borderTop: divider ? '1px solid ' + BORDER : 'none', fontSize: 12 } },
    React.createElement('span', { style: { opacity: 0.75 } }, label),
    React.createElement('span', null, value));
}

function Row({ st, open, onToggle }) {
  // Right of the bar: proof state "<proven> / <total>", same font/size as the machine name.
  const meta = st.proven + ' / ' + st.total;

  let detail;
  if (!st.importing && Array.isArray(st.summary)) {
    detail = st.summary.map((row, i) => React.createElement(StatRow, { key: row[0], label: row[0], value: row[1], divider: i > 0 }));
  } else {
    detail = [
      React.createElement(StatRow, { key: 't', label: 'subgoals', value: st.total, divider: false }),
      React.createElement(StatRow, { key: 'p', label: 'proven', value: st.proven }),
      React.createElement(StatRow, { key: 'y', label: 'sorried', value: st.sorried })
    ];
  }

  return React.createElement('div', { style: { border: '2px solid ' + BORDER, borderRadius: 6, overflow: 'hidden' } },
    React.createElement('div', {
      onClick: () => onToggle(st.machine),
      style: { display: 'flex', alignItems: 'center', gap: 10, padding: '10px 14px', cursor: 'pointer' }
    },
      React.createElement('span', { style: SLOT }, React.createElement(StatusIcon, { st })),
      React.createElement('span', { style: { fontSize: 12, fontWeight: 600, flexShrink: 0, maxWidth: 140, overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' } }, st.machine),
      React.createElement(ProgressBar, { st }),
      React.createElement('span', { style: { fontSize: 12, fontWeight: 600, flexShrink: 0 } }, meta),
      React.createElement('span', {
        style: { display: 'inline-flex', flexShrink: 0, transform: open ? 'rotate(180deg)' : 'rotate(0deg)', transition: 'transform 0.15s' },
        dangerouslySetInnerHTML: { __html: CHEVRON_SVG }
      })),
    open ? React.createElement('div', { style: { borderTop: '1px solid ' + BORDER } },
      React.createElement('div', { style: { padding: '2px 14px 6px' } }, detail)) : null);
}

export default function (_props) {
  const rs = useRpcSession();
  const [sts, setSts] = React.useState([]);
  const [openMap, setOpen] = React.useState({});
  const [paneOpen, setPaneOpen] = React.useState(true);

  React.useEffect(() => {
    let live = true;
    const tick = () => {
      rs.call('Barrel.Progress.get', null).then(r => { if (live) setSts(r); }).catch(() => { });
    };
    tick();
    const id = setInterval(tick, 300);
    return () => { live = false; clearInterval(id); };
  }, [rs]);

  // Global panel: stack every reported card inside a foldable "Progress" pane (like the
  // infoview's own "Tactic state" / "All Messages"). Renders nothing until an import reports,
  // so an idle panel is invisible. Park the cursor on any already-elaborated line (e.g. the
  // file header) to watch imports fill in live.
  if (!sts || sts.length === 0) return null;

  const cards = sts.map((st, i) => React.createElement('div', { key: st.machine, style: { marginBottom: i < sts.length - 1 ? 10 : 0 } },
    React.createElement(Row, {
      st,
      open: !!openMap[st.machine],
      onToggle: m => setOpen(o => ({ ...o, [m]: !o[m] }))
    })));

  return React.createElement(React.Fragment, null,
    React.createElement('style', null, '@keyframes barrel-bob{0%,100%{transform:translateY(-1.5px)}50%{transform:translateY(1.5px)}}'),
    React.createElement('details',
      { open: paneOpen, onToggle: e => setPaneOpen(e.currentTarget.open) },
      React.createElement('summary', { className: 'mv2 pointer non-selectable' }, 'BARReL state'),
      React.createElement('div', { style: { padding: '4px 10px' } }, cards)));
}

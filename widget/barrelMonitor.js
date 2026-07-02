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
const BLUE = 'var(--vscode-progressBar-background, #0078d4)';
const TRACK_GRAY = 'color-mix(in srgb, var(--vscode-foreground, #888) 12%, transparent)';
const IMPORT_BLUE = 'color-mix(in srgb, var(--vscode-progressBar-background, #0078d4) 31%, transparent)';

// All four states share one 14×14 footprint, so the badge never changes the card's height.
const BADGE = { width: 14, height: 14, borderRadius: '50%', flexShrink: 0, boxSizing: 'border-box' };

function StatusIcon({ st }) {
  if (st.importing) {
    return React.createElement('span', {
      style: { ...BADGE, display: 'inline-block', border: '2px solid ' + BLUE, borderTopColor: 'transparent', animation: 'barrel-spin 0.8s linear infinite' }
    });
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
      React.createElement(StatusIcon, { st }),
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
    React.createElement('style', null, '@keyframes barrel-spin{to{transform:rotate(360deg)}}'),
    React.createElement('details',
      { open: paneOpen, onToggle: e => setPaneOpen(e.currentTarget.open) },
      React.createElement('summary', { className: 'mv2 pointer non-selectable' }, 'BARReL state'),
      React.createElement('div', { style: { padding: '4px 10px' } }, cards)));
}

/*
 * Infoview panel widget for BARReL import progress (see Barrel/Progress.lean).
 *
 * A global panel widget (registered in Barrel/Progress.lean): polls
 * `Barrel.Progress.get` every 300 ms and stacks one collapsible card per
 * imported machine inside a foldable "Progress" pane (like the infoview's own
 * "Tactic state" / "All Messages"). Renders nothing until an import reports, so an
 * idle panel is invisible. Click a row to expand into the full detail (live
 * subgoal counts while running, the summary table once finished). Open states (the
 * pane and each card) live in React state so they survive the poll re-renders.
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
const CHEVRON_SVG = '<svg width="12" height="12" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="4 6 8 10 12 6"></polyline></svg>';

function secs(ms) { return (ms / 1000).toFixed(1) + 's'; }

function StatusIcon({ finished }) {
  if (finished) {
    return React.createElement('span', {
      style: { display: 'inline-flex', width: 14, height: 14, borderRadius: '50%', background: 'var(--vscode-testing-iconPassed, #3c3)', alignItems: 'center', justifyContent: 'center', flexShrink: 0 },
      dangerouslySetInnerHTML: { __html: CHECK_SVG }
    });
  }
  return React.createElement('span', {
    style: { display: 'inline-block', width: 12, height: 12, borderRadius: '50%', border: '2px solid var(--vscode-progressBar-background, #0078d4)', borderTopColor: 'transparent', flexShrink: 0, animation: 'barrel-spin 0.8s linear infinite' }
  });
}

function ProgressBar({ pct, finished }) {
  const color = finished ? 'var(--vscode-testing-iconPassed, #3c3)' : 'var(--vscode-progressBar-background, #0078d4)';
  return React.createElement('div', { style: { flex: 1, position: 'relative', height: 4 } },
    React.createElement('div', { style: { position: 'absolute', inset: 0, borderRadius: 2, background: 'var(--vscode-progressBar-background, #888)', opacity: 0.25 } }),
    React.createElement('div', { style: { position: 'absolute', left: 0, top: 0, height: '100%', width: pct + '%', borderRadius: 2, background: color } }));
}

function StatRow({ label, value, divider = true }) {
  return React.createElement('div', { style: { display: 'flex', justifyContent: 'space-between', padding: '7px 2px', borderTop: divider ? '1px solid ' + BORDER : 'none', fontSize: 12 } },
    React.createElement('span', { style: { opacity: 0.75 } }, label),
    React.createElement('span', null, value));
}

function Row({ st, open, onToggle }) {
  const pct = st.nbPOs > 0 ? Math.min(100, Math.round(100 * st.po / st.nbPOs)) : 0;
  const meta = st.finished ? secs(st.elapsedMs) : (st.po + '/' + st.nbPOs + ' · ~' + secs(st.etaMs) + ' left');

  let detail;
  if (st.finished && Array.isArray(st.summary)) {
    detail = st.summary.map((row, i) => React.createElement(StatRow, { key: row[0], label: row[0], value: row[1], divider: i > 0 }));
  } else {
    detail = [
      React.createElement(StatRow, { key: 's', label: 'subgoals attempted', value: st.subgoals, divider: false }),
      React.createElement(StatRow, { key: 'a', label: 'auto-solved so far', value: st.solved }),
      React.createElement(StatRow, { key: 'l', label: 'leftover so far', value: st.leftover })
    ];
    if (st.current) {
      detail.push(React.createElement('div', { key: 'c', style: { marginTop: 6, fontSize: 11, opacity: 0.65, whiteSpace: 'nowrap', overflow: 'hidden', textOverflow: 'ellipsis' } }, '→ ' + st.current));
    }
  }

  return React.createElement('div', { style: { border: '2px solid ' + BORDER, borderRadius: 6, overflow: 'hidden' } },
    React.createElement('div', {
      onClick: () => onToggle(st.machine),
      style: { display: 'flex', alignItems: 'center', gap: 10, padding: '10px 14px', cursor: 'pointer' }
    },
      React.createElement(StatusIcon, { finished: st.finished }),
      React.createElement('span', { style: { fontSize: 12, fontWeight: 600, flexShrink: 0, maxWidth: 140, overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' } }, st.machine),
      React.createElement(ProgressBar, { pct, finished: st.finished }),
      React.createElement('span', { style: { fontSize: 11, opacity: 0.65, flexShrink: 0 } }, meta),
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

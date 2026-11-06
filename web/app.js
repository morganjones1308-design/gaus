"use strict";
/* Gaus main window. All text from outside (game names, results) goes in through textContent, never innerHTML. */
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
function el(tag, attrs, ...kids) {
  const n = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v === false || v == null) continue;
    if (k === "class") n.className = v;
    else if (k.startsWith("on")) n.addEventListener(k.slice(2), v);
    else if (k === "text") n.textContent = v;
    else n.setAttribute(k, v === true ? "" : v);
  }
  for (const c of kids.flat()) if (c != null && c !== false) n.append(c.nodeType ? c : document.createTextNode(String(c)));
  return n;
}
const api = new Proxy({}, { get: (_, name) => (...a) => window.pywebview.api[name](...a) });
const penSvg = () => {
  const s = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  s.setAttribute("viewBox", "0 0 50 50"); s.setAttribute("class", "pen"); s.setAttribute("aria-hidden", "true");
  const c = document.createElementNS("http://www.w3.org/2000/svg", "circle");
  c.setAttribute("cx", 25); c.setAttribute("cy", 25); c.setAttribute("r", 20); s.append(c); return s;
};
const tickSvg = (bad) => {
  const s = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  s.setAttribute("viewBox", "0 0 16 16"); s.setAttribute("class", bad ? "tick bad" : "tick"); s.setAttribute("aria-hidden", "true");
  const p = document.createElementNS("http://www.w3.org/2000/svg", "path");
  p.setAttribute("d", bad ? "M8 2.5v6.5M8 12.2v.8" : "M2.5 8.5l3.5 3.5 7.5-8");
  p.setAttribute("fill", "none"); p.setAttribute("stroke", "currentColor"); p.setAttribute("stroke-width", "2.4");
  p.setAttribute("stroke-linecap", "round"); p.setAttribute("stroke-linejoin", "round"); s.append(p); return s;
};

let S = null;            // full state from Python
let rows = [];
let selKey = "";
let filterLid = "";
let lastRowsJson = "";
let live = [];           // downloads being followed right now

/* ---------- small UI helpers ---------- */
function toast(msg, err) {
  const t = el("div", { class: "toast" + (err ? " err" : ""), role: err ? "alert" : "status", text: msg });
  $("#toasts").append(t);
  setTimeout(() => { t.classList.add("out"); setTimeout(() => t.remove(), 300); }, err ? 6000 : 3200);
}
function ask({ title = "Gaus", body = "", ok = "OK", cancel = "Cancel", danger = false }) {
  return new Promise((resolve) => {
    const d = $("#dlg-ask");
    $("#ask-title").textContent = title; $("#ask-body").textContent = body;
    const okb = $("#ask-ok"), cb = $("#ask-cancel");
    okb.textContent = ok; okb.className = "btn " + (danger ? "danger" : "primary");
    cb.textContent = cancel || ""; cb.hidden = !cancel;
    const done = (v) => { d.removeEventListener("close", onclose); okb.onclick = null; cb.onclick = null; d.close(); resolve(v); };
    const onclose = () => resolve(false);
    d.addEventListener("close", onclose, { once: true });
    okb.onclick = (e) => { e.preventDefault(); done(true); };
    cb.onclick = () => done(false);
    d.showModal(); okb.focus();
  });
}
const notice = (body, title = "Gaus") => ask({ title, body, cancel: null });
async function busy(btn, fn) {
  btn.classList.add("busy"); btn.setAttribute("aria-busy", "true");
  try { return await fn(); } finally { btn.classList.remove("busy"); btn.removeAttribute("aria-busy"); }
}
function apply(res) {
  if (!res) return false;
  if (res.error) { toast(res.error, true); return false; }
  if (res.state) setState(res.state);
  return true;
}
function wireDialog(d) {
  $$("[data-close]", d).forEach((b) => b.addEventListener("click", () => d.close()));
  d.addEventListener("click", (e) => { if (e.target === d) d.close(); });
}
function field(inputEl, errEl, msg) {
  if (inputEl) { if (msg) inputEl.setAttribute("aria-invalid", "true"); else inputEl.removeAttribute("aria-invalid"); }
  if (errEl) errEl.textContent = msg || "";
}

/* ---------- state ---------- */
function setState(st) {
  S = st; rows = st.rows || [];
  document.title = `${S.app.title} v${S.app.version}`;
  $("#version").textContent = `Version ${S.app.version}`;
  renderAccounts(); renderLaunchers(); renderRows(true); renderBanner(); renderManage(); maybeTour();
  if (st.prompt) window.Gaus.saverPrompt(st.prompt);
}
function activeAccount() { return S.accounts.find((a) => a.id === S.active); }

function renderAccounts() {
  const box = $("#account"); box.textContent = "";
  S.accounts.forEach((a) => box.append(el("option", { value: a.id, selected: a.id === S.active }, a.name + (a.enabled ? "" : " (off)"))));
}
$("#account").addEventListener("change", async (e) => apply(await api.switch_account(e.target.value)));
function renderLaunchers() {
  const acc = activeAccount(); const box = $("#lc-filter"); box.textContent = "";
  if (!acc || !acc.launchers.some((l) => l.id === filterLid)) filterLid = "";
  box.append(el("option", { value: "" }, "All games"));
  (acc ? acc.launchers : []).forEach((l) => box.append(el("option", { value: l.id, selected: l.id === filterLid }, l.name + (l.enabled ? "" : " (off)"))));
}
$("#lc-filter").addEventListener("change", (e) => { filterLid = e.target.value; renderRows(true); });
$("#g-search").addEventListener("input", () => renderRows(true));
/* accounts and launchers are looked after in Settings */
function renderManage() {
  const box = $("#manage"); if (!box) return;
  const open = box.querySelector("details[open]") ? true : box.dataset.open === "1";
  box.textContent = ""; box.dataset.open = open ? "1" : "";
  const acc = activeAccount();
  const line = (title, sub, ...btns) => el("div", { class: "setting" }, el("div", {}, el("div", { class: "t" }, title), sub ? el("div", { class: "d" }, sub) : null), el("div", { class: "row" }, ...btns));
  const small = (text, onclick, cls) => el("button", { class: "btn sm " + (cls || "ghost"), type: "button", onclick }, text);
  box.append(el("details", { class: "group", name: "settings", open: open || undefined },
    el("summary", {}, "Accounts and launchers"),
    line(acc.name, "The account you are using now", small("Edit", () => openAccount("edit")),
      S.accounts.length > 1 ? small("Delete", deleteAccount, "ghost danger") : null, small("New account", () => openAccount("new"), "")),
    ...acc.launchers.map((l) => line(l.name, `${l.games} game${l.games === 1 ? "" : "s"}` + (l.enabled ? "" : " · off"),
      small("Edit", () => openLauncher(l)), small("Remove", () => removeLauncher(l), "ghost danger"))),
    line("Using another launcher?", "", small("Add a launcher", () => openLauncher(null), ""))));
}
function renderBanner() {
  const b = $("#banner");
  if (S.update) {
    $("#banner-text").textContent = `Version ${S.update.version} is available (you have ${S.app.version})` + (S.update.notes ? ` – ${S.update.notes}` : "");
    b.classList.add("show");
  } else b.classList.remove("show");
}

const statusClass = (t) => /fail|problem|error|not found|could not|gave up|give up|stalled/i.test(t) ? "bad"
  : /updating|downloading|starting|launching|checking|waiting|watching|opening/i.test(t) ? "busy" : "";
function renderRows(force) {
  const term = $("#g-search").value.trim().toLowerCase();
  const list = rows.filter((r) => (!filterLid || r.lid === filterLid) && r.name.toLowerCase().includes(term));
  const json = JSON.stringify([list, selKey, filterLid]);
  if (!force && json === lastRowsJson) return;
  lastRowsJson = json;
  if (!list.some((r) => r.key === selKey)) selKey = list.length ? list[0].key : "";
  const body = $("#rows"); const hadFocus = body.contains(document.activeElement); body.textContent = "";
  list.forEach((r, i) => {
    const b = el("button", { type: "button", "aria-selected": r.key === selKey ? "true" : "false", "data-key": r.key, title: r.name,
      onclick: () => select(r.key), ondblclick: () => editGame(),
      onkeydown: (e) => {
        const n = list[i + (e.key === "ArrowDown" ? 1 : e.key === "ArrowUp" ? -1 : NaN)];
        if (n) { e.preventDefault(); select(n.key); $(`#rows button[data-key="${CSS.escape(n.key)}"]`)?.focus(); }
      } },
      el("span", { class: "n" }, r.name), el("span", { class: "s " + statusClass(r.status) }, r.enabled ? r.status : "Off"));
    body.append(el("li", { class: r.enabled ? "" : "off" }, b));
    if (hadFocus && r.key === selKey) b.focus();
  });
  renderGamePage();
}
function renderGamePage() {
  const r = selRow(); const acc = activeAccount(); const empty = $("#empty");
  $("#game-page").hidden = !r; empty.hidden = !!r; $("#g-more").open = false;
  if (!r) {
    empty.textContent = "";
    if (acc && !acc.launchers.length) empty.append(el("h3", {}, "Add your first launcher"), el("p", {}, "Tell Gaus which launcher you use: Steam, Epic, GOG, EA, Ubisoft, Battle.net, Riot, Xbox or any other."), el("button", { class: "btn primary", type: "button", onclick: () => openLauncher(null) }, "Add a launcher"));
    else if ($("#g-search").value.trim()) empty.append(el("h3", {}, "No matches"), el("p", {}, "No game in your list has that name."));
    else empty.append(el("h3", {}, "No games here yet"), el("p", {}, "Add a game and Gaus keeps it up to date for you."), el("button", { class: "btn primary", type: "button", onclick: openAddGame }, "Add a game"));
    return;
  }
  $("#gp-name").textContent = r.name;
  const art = r.cover ? `url("${r.cover}")` : "none";
  if ($("#hero").dataset.art !== art) { $("#hero").dataset.art = art; $("#hero").style.backgroundImage = art; }
  $("#gp-status").textContent = r.status; $("#gp-status").className = statusClass(r.status) === "bad" ? "newer" : "";
  $("#gp-next").textContent = r.next === "-" ? "None" : r.next === "no windows set" ? "Not scheduled" : `${r.next} SAST`;
  $("#gp-patched").textContent = r.patched === "-" ? "Unknown" : `${r.patched} SAST`;
  $("#gp-launcher").textContent = r.launcher;
  const build = $("#gp-build"); build.textContent = r.installed === "-" ? "Unknown" : r.installed;
  if (r.latest !== "-" && r.latest !== r.installed) build.append(el("span", { class: "newer" }, ` → ${r.latest}`));
  syncToolbar();
}
function select(key) {
  selKey = key;
  $$("#rows button").forEach((b) => b.setAttribute("aria-selected", b.dataset.key === key ? "true" : "false"));
  renderGamePage();
}
function syncToolbar() {
  const r = selRow(); if (!r) return;
  const now = live.find((i) => i.appid === r.appid); const t = $("#g-track");
  t.disabled = !r.precise || (now && !now.tracked);
  t.textContent = now && now.tracked ? "Stop tracking" : "Track download";
  t.title = !r.precise ? "Live tracking works for Steam games" : "";
  $("#g-saver").hidden = !now;
  $("#gp-live").hidden = !now;
  if (now) {
    const bar = $("#gp-live .bar"); bar.classList.toggle("indeterminate", now.progress == null);
    bar.firstElementChild.style.setProperty("--p", ((now.progress || 0) * 100).toFixed(1) + "%");
    $("#gp-live-text").textContent = now.detail || "Waiting for Steam…";
  }
}
const selRow = () => rows.find((r) => r.key === selKey);

/* ---------- downloads ---------- */
const coverOf = (appid) => { const r = rows.find((x) => x.appid === appid); return r && r.cover ? `url("${r.cover}")` : "none"; };
function renderLive(items) {
  live = items; const box = $("#live");
  $$(".live-card", box).forEach((c) => { if (!items.some((i) => String(i.appid) === c.dataset.appid)) c.remove(); });
  items.forEach((i) => {
    let c = box.querySelector(`[data-appid="${i.appid}"]`);
    if (!c) {
      c = el("article", { class: "live-card", "data-appid": i.appid },
        el("div", { class: "live-art", style: `background-image:${coverOf(i.appid)}` }),
        el("div", { class: "live-body" },
          el("div", { class: "live-head" }, el("span", { class: "live-tag" }, "LIVE"), el("h3", {}, i.name), el("span", { class: "live-status" })),
          el("div", { class: "bar" }, el("i")), el("p", { class: "live-detail" }), el("p", { class: "live-note" }),
          el("div", { class: "live-btns" },
            el("button", { class: "btn sm", type: "button", onclick: () => openSaver(i) }, "Screen saver"),
            el("button", { class: "btn sm ghost stop", type: "button", onclick: () => setTracking(i.appid, i.name, false) }, "Stop tracking"))));
      box.append(c);
    }
    $(".live-status", c).textContent = i.status;
    $(".live-detail", c).textContent = i.detail || "Waiting for Steam…";
    $(".live-note", c).textContent = i.note;
    $(".stop", c).hidden = !i.tracked;
    const bar = $(".bar", c); bar.classList.toggle("indeterminate", i.progress == null);
    bar.firstElementChild.style.setProperty("--p", ((i.progress || 0) * 100).toFixed(1) + "%");
  });
  const n = items.length; const count = $("#dl-count");
  count.hidden = !n; count.textContent = n;
  $("#dl-sub").textContent = n ? "" : "Nothing is downloading. Updates you start in Steam show up here by themselves.";
  const dock = $("#dock"); dock.textContent = "";
  const first = items[0];
  if (first) {
    const bar = el("div", { class: "bar" + (first.progress == null ? " indeterminate" : "") }, el("i", { style: `--p:${((first.progress || 0) * 100).toFixed(1)}%` }));
    dock.append(el("b", {}, first.name), el("span", {}, `${first.status}` + (n > 1 ? `  ·  ${n - 1} more` : "")), bar);
  } else dock.append("No downloads");
  syncToolbar();
}
async function setTracking(appid, name, on) {
  await api.track(appid, on);
  toast(on ? `Tracking ${name}…` : `Stopped tracking ${name}. The download carries on.`);
}
$("#dock").onclick = () => showTab("downloads");

/* ---------- screen saver ---------- */
const svDlg = $("#dlg-saver"); wireDialog(svDlg);
let svItem = null;
function openSaver(item) {
  if (svDlg.open) return;
  svItem = item;
  $("#sv-sub").textContent = `${item.name} is downloading. Gaus can show its art full screen with the download progress, and darken the screen until it's done.`;
  const pick = (name, v) => { const i = $(`input[name="${name}"][value="${v}"]`) || $(`input[name="${name}"]`); i.checked = true; };
  pick("sv-dim", S.settings.saver_dim); pick("sv-others", S.settings.saver_others); pick("sv-src", S.settings.saver_source);
  $("#sv-never").checked = !S.settings.saver_ask;
  refreshPics();
  svDlg.showModal(); $("#sv-ok").focus();
}
/* the user's own pictures. Gaus art stays the default until they choose otherwise */
const picsDlg = $("#dlg-pics"); wireDialog(picsDlg);
let pics = [];
function drawPics() {
  const box = $("#pics"); box.textContent = "";
  pics.forEach((p) => box.append(el("button", { class: "thumb", type: "button", title: `Remove ${p.title}`, "aria-label": `Remove ${p.title}`, style: `background-image:url("${p.url}")`,
    onclick: async () => { pics = await api.remove_saver_image(p.file); drawPics(); } })));
  $("#pics-empty").hidden = !!pics.length;
  const n = pics.length; const label = n ? `${n} picture${n === 1 ? "" : "s"} · Edit` : "Choose pictures";
  [$("#sv-pics"), $("#set-pics")].forEach((b) => { if (b) b.textContent = label; });
}
async function refreshPics() { pics = await api.saver_images(); drawPics(); }
async function openPics() { await refreshPics(); picsDlg.showModal(); }
$("#pics-add").onclick = (e) => busy(e.currentTarget, async () => {
  const r = await api.add_saver_images();
  if (r.error) return toast(r.error, true);
  if (r.skipped) toast(`${r.skipped} skipped: too small, not a picture, or already added.`, true);
  await refreshPics();
});
picsDlg.addEventListener("close", () => {   // "My pictures" without any pictures falls back to Gaus art
  if (pics.length) return;
  $('input[name="sv-src"][value="gaus"]').checked = true;
  if (settingInputs.saver_source) settingInputs.saver_source.set("gaus");
});
$("#sv-pics").onclick = openPics;
$$('input[name="sv-src"]').forEach((i) => i.addEventListener("change", () => { if (i.value === "mine" && !pics.length) openPics(); }));
$("#sv-no").onclick = async () => {
  if ($("#sv-never").checked) { S.settings.saver_ask = false; if (settingInputs.saver_ask) settingInputs.saver_ask.set(false); apply(await api.save_settings({ saver_ask: false })); }
  svDlg.close();
};
$("#dlg-saver form").addEventListener("submit", async (e) => {
  e.preventDefault();
  const dim = +$('input[name="sv-dim"]:checked').value, others = $('input[name="sv-others"]:checked').value, source = $('input[name="sv-src"]:checked').value;
  await busy($("#sv-ok"), async () => {
    const res = await api.start_saver(svItem.appid, dim, others, source, !$("#sv-never").checked);
    if (apply(res)) svDlg.close();
  });
});
$("#g-saver").onclick = () => { const r = selRow(); const now = r && live.find((i) => i.appid === r.appid); if (now) openSaver(now); };

/* ---------- accounts ---------- */
const accDlg = $("#dlg-account"); wireDialog(accDlg);
let accMode = null;
function openAccount(mode) {
  accMode = mode; const a = activeAccount();
  $("#acc-title").textContent = mode === "new" ? "New account" : mode === "welcome" ? `Welcome to ${S.app.title}` : "Edit account";
  $("#acc-sub").textContent = mode === "welcome" ? "Whose account is this? A name is all it needs, no password." : "No password needed. An account only keeps people's launchers and games apart.";
  $("#acc-name").value = mode === "new" ? "" : a.name;
  $("#acc-enabled").checked = mode === "new" ? true : a.enabled;
  field($("#acc-name"), $("#acc-err"), "");
  accDlg.showModal(); $("#acc-name").focus(); $("#acc-name").select();
}
accDlg.addEventListener("cancel", (e) => { if (accMode === "welcome") e.preventDefault(); });
$("#dlg-account form").addEventListener("submit", async (e) => {
  e.preventDefault();
  const name = $("#acc-name").value.trim();
  if (!name) return field($("#acc-name"), $("#acc-err"), "Type a name first.");
  const btn = $("#acc-ok");
  await busy(btn, async () => {
    if (accMode === "new") {
      const res = await api.add_account(name);
      if (apply(res)) { accDlg.close(); if (await ask({ title: "Add a launcher?", body: `Add a launcher for ${name} now?`, ok: "Add launcher", cancel: "Later" })) openLauncher(null); }
    } else if (accMode === "welcome") {
      accMode = null; apply(await api.welcome_done(name)); accDlg.close(); maybeTour();
    } else {
      const a = activeAccount(); apply(await api.edit_account(a.id, name, $("#acc-enabled").checked)); accDlg.close();
    }
  });
});
async function deleteAccount() {
  const a = activeAccount(); if (!a || S.accounts.length <= 1) return notice("You need at least one account.");
  const n = a.launchers.reduce((s, l) => s + l.games, 0);
  if (await ask({ title: "Delete account", body: `Delete the account ${a.name} with its ${a.launchers.length} launcher(s) and ${n} game(s)? Nothing is uninstalled.`, ok: "Delete", danger: true }))
    apply(await api.remove_account(a.id));
}

/* ---------- launchers ---------- */
const lcDlg = $("#dlg-launcher"); wireDialog(lcDlg);
let lcEditing = null; let lcPrevDefault = "";
function fillLauncherTypes() {
  const sel = $("#lc-type"); sel.textContent = "";
  Object.entries(S.launcher_types).forEach(([k, v]) => sel.append(el("option", { value: k }, v.name)));
}
async function probeLauncher() {
  const key = $("#lc-type").value;
  const p = await api.launcher_probe(key);
  $("#lc-path-label").textContent = p.label;
  $("#lc-path").placeholder = p.placeholder;
  $("#lc-tip").textContent = p.tip;
  if (!lcEditing) {
    const nm = $("#lc-name");
    if (!nm.value.trim() || nm.value === lcPrevDefault) nm.value = p.default_name;
    lcPrevDefault = p.default_name;
  }
}
function openLauncher(lc) {
  lcEditing = lc; fillLauncherTypes(); field($("#lc-path"), $("#lc-err"), "");
  $("#lc-title").textContent = lc ? "Launcher settings" : "Add a launcher";
  $("#lc-type").value = lc ? lc.type : "steam"; $("#lc-type").disabled = !!lc;
  $("#lc-name").value = lc ? lc.name : ""; $("#lc-path").value = lc ? lc.path : "";
  $("#lc-args").value = lc ? lc.args : ""; $("#lc-enabled").checked = lc ? lc.enabled : true; lcPrevDefault = "";
  probeLauncher(); lcDlg.showModal(); $("#lc-name").focus();
}
$("#lc-type").addEventListener("change", probeLauncher);
$("#lc-browse").onclick = async () => {
  const p = await api.browse($("#lc-type").value === "steam" ? "folder" : "file");
  if (p) $("#lc-path").value = p;
};
$("#dlg-launcher form").addEventListener("submit", async (e) => {
  e.preventDefault();
  const data = { type: $("#lc-type").value, name: $("#lc-name").value.trim(), path: $("#lc-path").value.trim(), args: $("#lc-args").value.trim(), enabled: $("#lc-enabled").checked };
  await busy($("#lc-ok"), async () => {
    let res;
    if (lcEditing) res = await api.update_launcher(lcEditing.id, data.name, data.path, data.args, data.enabled);
    else {
      res = await api.add_launcher(data.type, data.name, data.path, data.args, data.enabled, false);
      if (res && res.needs_confirm) {
        if (!(await ask({ title: "Launcher not found", body: res.needs_confirm, ok: "Add anyway" }))) return;
        res = await api.add_launcher(data.type, data.name, data.path, data.args, data.enabled, true);
      }
    }
    if (res && res.error) return field($("#lc-path"), $("#lc-err"), res.error);
    if (res && res.lid) filterLid = res.lid;
    if (apply(res)) lcDlg.close();
  });
});
async function removeLauncher(l) {
  if (await ask({ title: "Remove launcher", body: `Remove ${l.name} and its ${l.games} game(s) from this account? Nothing is uninstalled.`, ok: "Remove", danger: true })) apply(await api.remove_launcher(l.id));
}

/* ---------- add game ---------- */
const agDlg = $("#dlg-addgame"); wireDialog(agDlg);
let agChoice = null; let agInstalled = []; let agSeq = 0;
function agLauncher() { return activeAccount().launchers.find((l) => l.id === $("#ag-launcher").value); }
function agList(items, emptyText) {
  const box = $("#ag-results"); box.textContent = "";
  agChoice = null;
  if (!items.length) { box.append(el("div", { class: "none" }, emptyText)); return; }
  items.forEach((r, i) => {
    const b = el("button", { type: "button", class: "result", role: "option", "aria-selected": "false",
      onclick: () => pick(b, r), ondblclick: () => { pick(b, r); $("#dlg-addgame form").requestSubmit(); },
      onkeydown: (e) => {
        const sib = e.key === "ArrowDown" ? b.nextElementSibling : e.key === "ArrowUp" ? b.previousElementSibling : null;
        if (sib) { e.preventDefault(); sib.focus(); pick(sib, items[Array.from(box.children).indexOf(sib)]); }
      } },
      el("span", {}, r.name), el("span", { class: "m" }, r.meta));
    box.append(b);
  });
  function pick(b, r) { $$(".result", box).forEach((x) => x.setAttribute("aria-selected", "false")); b.setAttribute("aria-selected", "true"); agChoice = r; field(null, $("#ag-err"), ""); }
}
function agMode() {
  const lc = agLauncher(); agChoice = null; field(null, $("#ag-err"), "");
  const steam = lc.type === "steam";
  $("#ag-search").textContent = steam ? "Search" : "Filter";
  $("#ag-intro").textContent = steam ? "Type the game title. Steam's store and your installed games are searched."
    : `Type the game title exactly as it appears in ${lc.name}. Games it has installed are listed when Gaus can read them.`;
  if (steam) agList([], "Search to see results.");
  else { agList([], "Loading…"); const seq = ++agSeq; api.installed_games(lc.id).then((list) => {
    if (seq !== agSeq) return; agInstalled = list; agFilter();
    if (!list.length) $("#ag-intro").textContent = `Gaus cannot list ${lc.name}'s games, so type the title and press Add game.`; }); }
}
function agFilter() {
  const t = $("#ag-term").value.trim().toLowerCase();
  const items = agInstalled.filter((g) => g.name.toLowerCase().includes(t)).map((g) => ({ ...g, meta: "installed" + (g.dup ? " · already added" : "") }));
  agList(items, agInstalled.length ? "Nothing listed matches. Press Add game to use the title you typed." : "Nothing to list. Type the title and press Add game.");
}
async function agSearch() {
  const lc = agLauncher();
  if (lc.type !== "steam") return agFilter();
  const term = $("#ag-term").value.trim(); if (!term) return;
  await busy($("#ag-search"), async () => {
    agList([], "Searching…");
    const res = await api.search_games(lc.id, term);
    if (res.error) { agList([], ""); return field(null, $("#ag-err"), "Search failed: " + res.error); }
    agList(res.results.map((r) => ({ ...r, meta: `AppID ${r.appid}` + (r.installed ? " · installed" : "") + (r.dup ? " · already added" : "") })), "Nothing found. Try another spelling.");
  });
}
function openAddGame() {
  const acc = activeAccount();
  if (!acc.launchers.length) { notice("Add a launcher to this account first.").then(() => openLauncher(null)); return; }
  const sel = $("#ag-launcher"); sel.textContent = "";
  acc.launchers.forEach((l) => sel.append(el("option", { value: l.id }, l.name)));
  sel.value = filterLid || acc.launchers[0].id; $("#ag-term").value = ""; agMode();
  agDlg.showModal(); $("#ag-term").focus();
}
$("#ag-launcher").addEventListener("change", agMode);
$("#ag-search").onclick = agSearch;
$("#ag-term").addEventListener("keydown", (e) => { if (e.key === "Enter") { e.preventDefault(); agSearch(); } });
$("#ag-term").addEventListener("input", () => { if (agLauncher().type !== "steam") agFilter(); });
$("#dlg-addgame form").addEventListener("submit", async (e) => {
  e.preventDefault(); const lc = agLauncher(); const typed = $("#ag-term").value.trim();
  let name, appid = null;
  if (agChoice) { name = agChoice.name; appid = agChoice.appid; if (agChoice.dup) return field(null, $("#ag-err"), "That game is already in this launcher."); }
  else if (lc.type !== "steam" && typed) name = typed;
  else return field(null, $("#ag-err"), lc.type === "steam" ? "Pick a game from the list first." : "Type the game's title first.");
  await busy($("#ag-ok"), async () => {
    const res = await api.add_game(lc.id, name, appid);
    if (res && res.error) return field(null, $("#ag-err"), res.error);
    filterLid = lc.id; if (apply(res)) { agDlg.close(); toast(`Added ${name}`); }
  });
});
$("#g-add").onclick = openAddGame;

/* ---------- schedule ---------- */
const gmDlg = $("#dlg-game"); wireDialog(gmDlg);
let gmRow = null;
async function editGame() {
  const r = selRow(); if (!r) return notice("Select a game in the list first.");
  const d = await api.game_detail(r.lid, r.appid); if (d.error) return toast(d.error, true);
  gmRow = r; $("#gm-title").textContent = `${d.name} – schedule and photos`;
  $("#gm-enabled").checked = d.enabled; $("#gm-weekly").value = d.weekly; $("#gm-dates").value = d.dates; $("#gm-kw").value = d.keywords;
  $("#gm-wu").checked = !!d.warmup; $("#gm-wu-quiet").value = d.warmup_quiet; $("#gm-wu-max").value = d.warmup_max;
  $("#gm-wu-box").hidden = !d.steam; syncWarmup();
  $("#gm-err").textContent = ""; gmDlg.showModal(); $("#gm-weekly").focus();
}
function syncWarmup() { const on = $("#gm-wu").checked; $("#gm-wu-quiet").disabled = !on; $("#gm-wu-max").disabled = !on; $("#gm-wu-opts").style.opacity = on ? "1" : ".5"; }
$("#gm-wu").addEventListener("change", syncWarmup);
$("#g-edit").onclick = editGame;
$("#gm-images").onclick = (e) => busy(e.currentTarget, async () => {
  const r = await api.add_images(gmRow.lid, gmRow.appid);
  if (r.error) toast(r.error, true); else if (r.added) toast(`Added ${r.added} image${r.added > 1 ? "s" : ""}` + (r.skipped ? ` (${r.skipped} skipped: too small or not a picture)` : "")); else if (r.skipped) toast("Those images were too small or not pictures (at least 640×360).", true);
});
$("#dlg-game form").addEventListener("submit", async (e) => {
  e.preventDefault();
  await busy($("#gm-ok"), async () => {
    const res = await api.save_game(gmRow.lid, gmRow.appid, $("#gm-enabled").checked, $("#gm-weekly").value, $("#gm-dates").value, $("#gm-kw").value,
      $("#gm-wu").checked, parseInt($("#gm-wu-max").value, 10) || 45, parseInt($("#gm-wu-quiet").value, 10) || 3);
    if (res && res.error) { $("#gm-err").textContent = res.error; return; }
    if (apply(res)) { gmDlg.close(); toast("Schedule saved"); }
  });
});
$("#g-del").onclick = async () => {
  const r = selRow(); if (!r) return notice("Select a game in the list first.");
  if (await ask({ title: "Remove game", body: `Remove ${r.name} from this launcher? Its downloaded photos are deleted when no account uses it any more.`, ok: "Remove", danger: true })) apply(await api.remove_game(r.lid, r.appid));
};
$("#g-track").onclick = () => { const r = selRow(); if (r) setTracking(r.appid, r.name, !live.some((i) => i.appid === r.appid)); };
$("#g-check").onclick = async () => { const r = selRow(); if (r) { await api.check_now(r.appid); toast(`Checking ${r.name}…`); } };
$("#g-check-all").onclick = async () => { await api.check_now(null); toast("Checking all games…"); };
$("#g-preview").onclick = async () => { const r = selRow(); if (!r) return; const res = await api.preview(r.appid); if (res && res.message) notice(res.message); };
$("#g-photos").onclick = async () => {
  const r = selRow(); if (!r) return;
  if (await ask({ title: "Refresh photos", body: "Replace this game's photos with a fresh set?", ok: "Replace" })) { await api.refresh_photos(r.appid); toast("Fetching new photos…"); }
};

/* ---------- stats for nerds ---------- */
let statsTimer = 0;
const pc = (v) => v == null ? "…" : `${v.toFixed(v < 10 ? 2 : 1)}%`;
const mins = (s) => s < 3600 ? `${Math.round(s / 60)} min` : `${Math.floor(s / 3600)} h ${Math.round(s % 3600 / 60)} min`;
async function drawStats() {
  const d = await api.nerd_stats();
  if (d.error) { $("#st-engine").textContent = d.error; return; }
  $("#st-ram").textContent = `${Math.round(d.ram_mb)} MB`;
  $("#st-ram-sub").textContent = `${d.ram_of_pc_pc.toFixed(1)}% of ${d.pc_ram_gb.toFixed(0)} GB`;
  $("#st-cpu").textContent = pc(d.cpu_pc);
  $("#st-cpu-sub").textContent = d.cpu_pc == null ? "Measuring…" : `Across ${d.cores} logical cores`;
  $("#st-tray").textContent = d.tray ? `${Math.round(d.tray.ram_mb)} MB` : "Not yet";
  $("#st-tray-sub").textContent = d.tray ? `${pc(d.tray.cpu_pc)} CPU, at ${d.tray.when}` : "Measured about 50 seconds after you close the window to the tray";
  const body = $("#st-rows"); body.textContent = "";
  d.rows.forEach((r) => body.append(el("tr", {}, el("td", {}, r.role), el("td", {}, String(r.pid)), el("td", { class: "num" }, r.ram.toFixed(1)),
    el("td", { class: "num" }, r.commit.toFixed(1)), el("td", { class: "num" }, pc(r.cpu)), el("td", { class: "num" }, String(r.threads)))));
  body.append(el("tr", { class: "sum" }, el("td", {}, "Total"), el("td", {}), el("td", { class: "num" }, d.ram_mb.toFixed(1)), el("td", { class: "num" }, d.commit_mb.toFixed(1)), el("td", { class: "num" }, pc(d.cpu_pc)), el("td", {})));
  $("#st-engine").textContent = `Running for ${mins(d.uptime_s)}, ${d.cpu_total_s.toFixed(0)} seconds of CPU time so far. The last update check took ${d.tick_ms.toFixed(1)} ms of CPU, and that check runs every ${d.tick_s} seconds.`;
}

/* ---------- tabs ---------- */
function showTab(name) {
  ["games", "downloads", "settings", "log", "guide", "stats"].forEach((n) => {
    $("#tab-" + n).setAttribute("aria-selected", String(n === name));
    $("#p-" + n).classList.toggle("show", n === name);
  });
  clearInterval(statsTimer);          // only measure while someone is looking
  if (name === "stats") { drawStats(); statsTimer = setInterval(drawStats, 2000); }
  if (name === "log") { const l = $("#log"); l.scrollTop = l.scrollHeight; }
}
$$("nav.tabs button").forEach((b, i, all) => {
  b.addEventListener("click", () => showTab(b.id.replace("tab-", "")));
  b.addEventListener("keydown", (e) => {
    if (e.key !== "ArrowDown" && e.key !== "ArrowUp") return;
    e.preventDefault();
    const n = all[(i + (e.key === "ArrowDown" ? 1 : all.length - 1)) % all.length]; n.focus(); n.click();
  });
});

/* ---------- settings ---------- */
const AFTER_NOTES = { sleep: "The PC sleeps, and Gaus can wake it again for the next window.", hibernate: "The PC hibernates, and Gaus can wake it again for the next window.", shutdown: "The PC shuts down. A shut-down PC can NOT wake itself, so switch it on yourself before the next window." };
const SCHEMA = [
  { group: "Finding updates", items: [
    { key: "auto_track", type: "toggle", title: "Track Steam downloads I start myself", desc: "Shows live progress for your games here. Tracking never opens Steam, and it keeps the PC awake until the download ends." },
    { key: "remote_check", type: "toggle", title: "Steam: check the latest build first", desc: "Asks api.steamcmd.net before opening Steam, so Steam is only opened when there is something to get." },
    { key: "remote_poll_seconds", type: "number", title: "Re-check every", min: 60, max: 3600, step: 30, unit: "sec" },
    { key: "start_early_minutes", type: "number", title: "Start watching before the window", min: 0, max: 60, unit: "min" },
    { key: "watch_minutes", type: "number", title: "Keep watching after the window starts", min: 15, max: 720, step: 15, unit: "min" },
    { key: "stall_minutes", type: "number", title: "Give up if no update starts", min: 5, max: 240, step: 5, unit: "min" },
    { key: "generic_quiet_minutes", type: "number", title: "Other launchers: finished after this many quiet minutes", desc: "Gaus cannot ask them for a build number, so it watches their disk activity instead.", min: 1, max: 60, unit: "min" } ] },
  { group: "When updates are done", items: [
    { key: "shutdown_enabled", type: "toggle", title: "Power the PC down when updates have finished" },
    { key: "shutdown_after_manual", type: "toggle", title: "Also after downloads I start myself", desc: "Includes Track and Check now. Off means only scheduled updates power the PC down. Open programs are closed, so save your work." },
    { key: "after_action", type: "radio", title: "…by doing this", options: [["Sleep", "sleep"], ["Hibernate", "hibernate"], ["Shut down", "shutdown"]], note: true },
    { key: "shutdown_idle_minutes", type: "number", title: "…only if nobody used the PC for", min: 1, max: 120, unit: "min" },
    { key: "shutdown_wait_minutes", type: "number", title: "…stop waiting for that after", min: 5, max: 480, step: 5, unit: "min" },
    { key: "countdown_seconds", type: "number", title: "Cancel countdown", min: 10, max: 600, step: 10, unit: "sec" },
    { key: "close_steam_before_shutdown", type: "toggle", title: "Close Steam cleanly before powering down" },
    { key: "dry_run_shutdown", type: "toggle", title: "Dry run", desc: "Do everything but do NOT power down. For testing." } ] },
  { group: "Waking the PC", items: [
    { key: "wake_from_sleep", type: "toggle", title: "Wake the PC from sleep or hibernate before each window" },
    { key: "wake_lead_minutes", type: "number", title: "…wake it this long before watching starts", min: 1, max: 30, unit: "min" },
    { custom: "wake" } ] },
  { group: "Screen saver", items: [
    { key: "saver_ask", type: "toggle", title: "Offer the screen saver when a download starts", desc: "You can also start it any time from Downloads." },
    { key: "saver_source", type: "radio", title: "Pictures", options: [["Gaus art", "gaus"], ["My pictures", "mine"]], desc: "Gaus art shows the game that's updating." },
    { custom: "pics" },
    { key: "saver_dim", type: "radio", title: "How dark this screen goes", options: [["A little", "30"], ["Dim", "60"], ["Very dim", "80"]] },
    { key: "saver_others", type: "radio", title: "Other monitors", options: [["Leave on", "keep"], ["Dim", "dim"], ["Turn black", "black"]], desc: "They stay powered. “Turn black” covers them with solid black." } ] },
  { group: "Loading screen", items: [
    { key: "loading_screen", type: "radio", title: "Show it", options: [["Auto", "auto"], ["Fullscreen", "fullscreen"], ["Window", "windowed"], ["Off", "off"]], desc: "Auto means fullscreen when nobody is using the PC, otherwise a window." },
    { key: "slide_seconds", type: "number", title: "Seconds per photo", min: 3, max: 30, unit: "sec" },
    { key: "photos_per_game", type: "number", title: "Photos per game", min: 8, max: 60, step: 4, unit: "photos" } ] },
  { group: "This app", items: [
    { key: "start_with_windows", type: "toggle", title: "Start with Windows", desc: "Runs quietly in the tray." },
    { key: "paused", type: "toggle", title: "Pause all scheduling" },
    { key: "auto_update_check", type: "toggle", title: "Look for new versions of Gaus every few hours" },
    { key: "auto_install_updates", type: "toggle", title: "Install new versions by themselves", desc: "Game downloads keep going, and Gaus catches up with them when it restarts." },
    { key: "update_feed_url", type: "text", title: "Update feed URL", stack: true },
    { custom: "update" } ] },
];
const settingInputs = {};
function numberControl(it) {
  const inp = el("input", { type: "number", min: it.min, max: it.max, step: it.step || 1, inputmode: "numeric", "aria-label": it.title });
  const clamp = () => { let v = parseInt(inp.value, 10); if (isNaN(v)) v = it.min; inp.value = Math.min(it.max, Math.max(it.min, v)); };
  const bump = (d) => { clamp(); inp.value = Math.min(it.max, Math.max(it.min, (+inp.value) + d * (it.step || 1))); };
  inp.addEventListener("change", clamp);
  const wrap = el("div", { class: "row" },
    el("div", { class: "stepper" },
      el("button", { type: "button", "aria-label": "Decrease", onclick: () => bump(-1) }, "−"), inp,
      el("button", { type: "button", "aria-label": "Increase", onclick: () => bump(1) }, "+")),
    el("span", { class: "unit" }, it.unit || ""));
  settingInputs[it.key] = { get: () => { clamp(); return +inp.value; }, set: (v) => { inp.value = v; } };
  return wrap;
}
function buildSettings() {
  const root = $("#settings"); root.textContent = "";
  root.append(el("div", { id: "manage" }));
  SCHEMA.forEach((g) => {
    const box = el("details", { class: "group", name: "settings" }, el("summary", {}, g.group));
    g.items.forEach((it) => {
      if (it.custom === "pics") {
        box.append(el("div", { class: "setting" }, el("div", {}, el("div", { class: "t" }, "My screen saver"), el("div", { class: "d" }, "Pick the pictures it shows when “My pictures” is on.")),
          el("button", { class: "btn sm", type: "button", id: "set-pics", onclick: openPics }, "Choose pictures")));
        return;
      }
      if (it.custom === "wake") {
        const b1 = el("button", { class: "btn sm", type: "button", onclick: (e) => wakeCheck(e.currentTarget) }, "Check wake setup");
        const b2 = el("button", { class: "btn sm", type: "button", onclick: (e) => wakeTest(e.currentTarget) }, "Test wake (2 min)");
        box.append(el("div", { class: "setting" }, el("div", {}, el("div", { class: "t" }, "Is waking set up right?"), el("div", { class: "d" }, "Windows must allow wake timers, and the hardware must support them. The test is the proof.")), el("div", { class: "row" }, b1, b2)));
        return;
      }
      if (it.custom === "update") {
        const b = el("button", { class: "btn sm", type: "button", onclick: (e) => busy(e.currentTarget, async () => { await api.check_updates(true); }) }, "Check for updates now");
        box.append(el("div", { class: "setting" }, el("div", {}, el("div", { class: "t" }, `You have version ${S.app.version}`), el("div", { class: "d" }, "Gaus can update itself from your GitHub release.")), b));
        return;
      }
      const row = el("div", { class: "setting" + (it.stack ? " stack" : "") });
      const label = el("div", {}, el("div", { class: "t", id: "t-" + it.key }, it.title), it.desc ? el("div", { class: "d" }, it.desc) : null);
      let ctl;
      if (it.type === "toggle") {
        const inp = el("input", { type: "checkbox", "aria-labelledby": "t-" + it.key });
        ctl = el("label", { class: "switch" }, inp, el("span", { class: "track", "aria-hidden": "true" }));
        settingInputs[it.key] = { get: () => inp.checked, set: (v) => { inp.checked = !!v; }, node: inp };
      } else if (it.type === "number") ctl = numberControl(it);
      else if (it.type === "radio") {
        const grp = el("fieldset", { class: "seg", "aria-labelledby": "t-" + it.key });
        it.options.forEach(([lab, val]) => grp.append(el("label", {}, el("input", { type: "radio", name: "s-" + it.key, value: val }), el("span", {}, lab))));
        ctl = grp;
        settingInputs[it.key] = { get: () => (grp.querySelector("input:checked") || {}).value, set: (v) => { const i = grp.querySelector(`input[value="${v}"]`); if (i) i.checked = true; refreshNotes(); } };
        grp.addEventListener("change", refreshNotes);
      } else {
        const inp = el("input", { class: "input", type: "text", spellcheck: "false", autocomplete: "off", "aria-labelledby": "t-" + it.key });
        ctl = inp; settingInputs[it.key] = { get: () => inp.value.trim(), set: (v) => { inp.value = v || ""; inp.placeholder = S.app.feed_builtin ? "Built-in feed in use" : "https://github.com/OWNER/REPO/releases/latest/download/update.json"; } };
      }
      row.append(label, ctl);
      if (it.note) row.append(el("div", { class: "d", id: "note-" + it.key, role: "status", style: "grid-column:1/-1" }));
      box.append(row);
    });
    root.append(box);
  });
  const save = el("button", { class: "btn primary", type: "button", id: "save-settings", onclick: (e) => saveSettings(e.currentTarget) }, "Save settings");
  root.after(el("div", { class: "savebar" }, save, el("span", { class: "hint", id: "save-msg", role: "status" })));
  renderManage(); refreshPics();
}
function refreshNotes() { const n = $("#note-after_action"); if (n && settingInputs.after_action) n.textContent = AFTER_NOTES[settingInputs.after_action.get()] || ""; }
function fillSettings() { Object.entries(settingInputs).forEach(([k, c]) => c.set(S.settings[k])); refreshNotes(); }
async function saveSettings(btn) {
  const out = {}; Object.entries(settingInputs).forEach(([k, c]) => { out[k] = c.get(); });
  await busy(btn, async () => { if (apply(await api.save_settings(out))) toast("Settings saved"); });
}
async function wakeCheck(btn) {
  await busy(btn, async () => {
    const r = await api.wake_check();
    if (r.fixable) { if (await ask({ title: "Wake timers", body: r.message, ok: "Change it", cancel: "Not now" })) { const f = await api.wake_fix(); notice(f.message); } }
    else notice(r.message, "Wake timers");
  });
}
async function wakeTest(btn) { await busy(btn, async () => { const r = await api.wake_test(); notice(r.message, "Wake test"); }); }

/* ---------- log ---------- */
function addLog(line) {
  const l = $("#log"); const near = l.scrollHeight - l.scrollTop - l.clientHeight < 60;
  l.append(document.createTextNode(line + "\n"));
  while (l.childNodes.length > 2500) l.removeChild(l.firstChild);
  if (near) l.scrollTop = l.scrollHeight;
}
$("#open-data").onclick = () => api.open_data_folder();

/* ---------- app updates ---------- */
async function askInstall() {
  if (!S.update) return;
  const body = `Install version ${S.update.version} now? The app will restart.` + (S.update.notes ? `\n\n${S.update.notes}` : "");
  if (!(await ask({ title: "Update Gaus", body, ok: "Install and restart" }))) return;
  const res = await api.install_update();
  if (res && res.error) return notice(res.error);
  if (res && res.started) { $("#busy-title").textContent = "Updating Gaus"; $("#busy-text").textContent = "Downloading the update…"; setBar(0); $("#dlg-busy").showModal(); }
}
$("#dlg-busy").addEventListener("cancel", (e) => e.preventDefault());
$("#banner-btn").onclick = askInstall;
function setBar(p) { const b = $("#busy-bar"); b.classList.toggle("indeterminate", p == null); b.firstElementChild.style.setProperty("--p", (p || 0) + "%"); }

/* ---------- welcome tour ---------- */
const TOUR = [
  { at: "#tab-games", tab: "games", title: "Your Library", text: "Every game Gaus looks after is here. Select one to see when it next updates and what you can do with it." },
  { at: "#g-add", tab: "games", title: "Add your games", text: "Start here. Gaus keeps only the games you add up to date." },
  { at: ".actions", tab: "games", title: "One game, one place", text: "Check for an update, follow a download, or set a schedule so the game updates when it usually patches." },
  { at: "#tab-downloads", tab: "downloads", title: "Downloads", text: "Live progress appears here, even for Steam updates you started yourself. From here you can also start the screen saver, using Gaus art or your own pictures." },
  { at: "#dock", tab: "downloads", title: "Always in view", text: "This bar shows what's downloading from any page. Click it to jump to Downloads." },
  { at: "#tab-settings", tab: "settings", title: "Settings", text: "Add launchers, choose whether the PC shuts down or sleeps after updates, and set up the screen saver." },
  { at: "#tab-guide", tab: "guide", title: "That's the tour", text: "The Guide explains everything in more detail, and you can take this tour again from there." },
];
let tourAt = -1;
function maybeTour() {
  if (S.shown && !S.settings.tour_done && tourAt < 0 && !$("dialog[open]")) startTour();
}
function startTour() { $("#tour").hidden = false; tourAt = -1; tourMove(1); }
function tourMove(d) {
  let i = tourAt + d;
  const usable = (s) => { showTab(s.tab); const n = $(s.at); return n && n.getBoundingClientRect().width > 0; };
  while (TOUR[i] && !usable(TOUR[i])) i += d;       // no games yet means no game actions to point at
  if (!TOUR[i]) return d > 0 ? endTour() : undefined;
  tourAt = i; const s = TOUR[i];
  const r = $(s.at).getBoundingClientRect(); const hole = $("#tour-hole"); const card = $("#tour-card");
  Object.assign(hole.style, { left: r.left - 5 + "px", top: r.top - 5 + "px", width: r.width + 10 + "px", height: r.height + 10 + "px" });
  $("#tour-step").textContent = `${i + 1} of ${TOUR.length}`;
  $("#tour-title").textContent = s.title; $("#tour-text").textContent = s.text;
  $("#tour-back").hidden = i === 0;
  $("#tour-next").textContent = i === TOUR.length - 1 ? "Done" : "Next";
  const w = card.offsetWidth, h = card.offsetHeight, gap = 14;
  const left = r.right + gap + w < innerWidth ? r.right + gap : Math.max(gap, Math.min(r.left, innerWidth - w - gap));
  const beside = r.right + gap + w < innerWidth;
  const top = beside ? Math.max(gap, Math.min(r.top, innerHeight - h - gap)) : r.top - h - gap > 0 ? r.top - h - gap : Math.min(r.bottom + gap, innerHeight - h - gap);
  Object.assign(card.style, { left: left + "px", top: top + "px" });
  $("#tour-next").focus();
}
function endTour() {
  $("#tour").hidden = true; tourAt = -1; showTab("games");
  if (!S.settings.tour_done) { S.settings.tour_done = true; api.save_settings({ tour_done: true }); }
}
$("#tour-next").onclick = () => tourMove(1);
$("#tour-back").onclick = () => tourMove(-1);
$("#tour-skip").onclick = endTour;
$("#tour-again").onclick = startTour;
document.addEventListener("keydown", (e) => { if (e.key === "Escape" && tourAt >= 0) endTour(); });

/* ---------- bridge from Python ---------- */
window.Gaus = {
  state(st) { const first = !S; setState(st); if (first) { buildSettings(); fillSettings(); } },
  rows(r) { rows = r; renderRows(false); },
  live: renderLive,
  saverPrompt(item) { if (S && tourAt < 0) { showTab("downloads"); openSaver(item); } },
  log: addLog,
  update(info) { if (S) { S.update = info; renderBanner(); } },
  notice(text, title) { notice(text, title); },
  toast,
  paused(v) { if (S) S.settings.paused = v; if (settingInputs.paused) settingInputs.paused.set(v); },
  installProgress(p) { setBar(p); $("#busy-text").textContent = `Downloading the update… ${p}%`; },
  installFailed(msg) { $("#dlg-busy").close(); notice(msg, "The update could not be installed"); },
  askInstall() { showTab("games"); askInstall(); },
  showTab,
};

async function init() {
  const st = await api.ready();
  window.Gaus.state(st);
  (await api.log_tail()).forEach(addLog);
  if (st.first_run) openAccount("welcome");
}
if (window.pywebview && window.pywebview.api) init(); else window.addEventListener("pywebviewready", init);
document.addEventListener("contextmenu", (e) => { if (!/input|textarea/i.test(e.target.tagName)) e.preventDefault(); });

// The docs pages: the graph of where the file sits, the declarations as open cards and rows, the
// map of the file with the reader's place in it, and previews of in-page links.
(function () {
  "use strict";
  const $ = (id) => document.getElementById(id);
  const esc = (s) => String(s ?? "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const hoverable = matchMedia("(hover: hover)").matches;
  const reduce = matchMedia("(prefers-reduced-motion: reduce)").matches;

  // ---- the graph: theory above, papers on a year axis, the languages below
  const graph = $("graph");
  if (graph) {
    const G = JSON.parse($("graph-data").textContent), N = G.nodes, E = G.edges, FOCUS = G.focus;
    const W = 300, Y = { t: 24, s: 100, g: 100, f: 182 }, X0 = 16, X1 = 284;
    const years = Object.values(N).map((n) => n.y).filter(Boolean);
    const lo = Math.floor((Math.min(...years) - 3) / 10) * 10, hi = Math.max(Math.max(...years) + 3, lo + 20);
    const xOfYear = (y) => X0 + (y - lo) / (hi - lo) * (X1 - X0);
    const pos = {};
    // Papers sit at their year; two in one place stagger up and down.
    const papers = Object.keys(N).filter((id) => N[id].y).sort((a, b) => N[a].y - N[b].y);
    papers.forEach((id, i) => {
      const x = xOfYear(N[id].y), prev = papers[i - 1];
      const clash = prev && Math.abs(pos[prev].x - x) < 9;
      pos[id] = { x, y: Y.s + (clash ? 9 : 0) };
      if (clash && pos[prev].y === Y.s) pos[prev].y = Y.s - 9;
    });
    // The other bands spread evenly across the width, in the order of the mean year of their papers.
    for (const k of ["t", "f"]) {
      const ids = Object.keys(N).filter((id) => N[id].k === k);
      const bary = (id) => {
        const xs = E.filter((e) => e[2] !== "cite" && (e[1] === id || e[0] === id)).map((e) => pos[e[0] === id ? e[1] : e[0]]).filter(Boolean).map((p) => p.x);
        return xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : (X0 + X1) / 2;
      };
      const order = ids.map((id) => [id, bary(id)]).sort((a, b) => a[1] - b[1]);
      const step = (X1 - X0) / Math.max(1, order.length);
      order.forEach((o, i) => { pos[o[0]] = { x: X0 + step * (i + 0.5), y: Y[k] }; });
    }
    const svg = $("g"), tip = $("tip");
    const curve = (a, b) => { const m = (a.y + b.y) / 2; return `M${a.x},${a.y} C${a.x},${m} ${b.x},${m} ${b.x},${b.y}`; };
    const arc = (a, b) => { const dip = Math.max(a.y, b.y) + 16 + Math.min(30, Math.abs(a.x - b.x) * 0.25); return `M${a.x},${a.y} C${a.x},${dip} ${b.x},${dip} ${b.x},${b.y}`; };
    const shape = (id) => {
      const n = N[id], p = pos[id], foc = id === FOCUS;
      if (n.k === "t") return `<rect class="t" x="${p.x - 4.5}" y="${p.y - 4.5}" width="9" height="9" rx="1.5"/>`;
      if (n.k === "f") return `<rect class="f" x="${p.x - 4}" y="${p.y - 4}" width="8" height="8" rx="1" transform="rotate(45 ${p.x} ${p.y})"/>`;
      if (n.k === "g") return `<circle class="g" cx="${p.x}" cy="${p.y}" r="4.6"/>`;
      return (foc ? `<circle class="ring" cx="${p.x}" cy="${p.y}" r="9"/>` : "") + `<circle class="s" cx="${p.x}" cy="${p.y}" r="${foc ? 6 : 4.6}"/>`;
    };
    let h = `<line class="axis" x1="${X0}" x2="${X1}" y1="${Y.s + 22}" y2="${Y.s + 22}"/>`;
    const step = hi - lo > 60 ? 20 : 10;
    for (let yr = Math.ceil(lo / step) * step; yr <= hi; yr += step) h += `<text class="tick" x="${xOfYear(yr)}" y="${Y.s + 34}">${yr}</text>`;
    h += E.filter((e) => pos[e[0]] && pos[e[1]]).map((e, i) => {
      const a = pos[e[0]], b = pos[e[1]];
      const cls = e[2] === "cite" ? "e lat" : "e" + (e[0] === FOCUS || e[1] === FOCUS ? " on" : "") + (e[2] === "weak" ? " weak" : "");
      return `<path class="${cls}" data-i="${E.indexOf(e)}" d="${e[2] === "cite" ? arc(a, b) : curve(a, b)}"/>`;
    }).join("");
    h += Object.keys(N).filter((id) => pos[id]).map((id) => `<a class="n${id === FOCUS ? " focus" : ""}" data-id="${esc(id)}" href="${esc(N[id].h)}" aria-label="${esc(N[id].l)}">` +
      `<circle class="hit" cx="${pos[id].x}" cy="${pos[id].y}" r="10"/>${shape(id)}</a>`).join("");
    svg.innerHTML = h;

    const light = (id, withTip) => {
      graph.classList.toggle("hovering", !!id);
      const near = new Set();
      svg.querySelectorAll(".e").forEach((p) => {
        const e = E[+p.dataset.i], hit = !!id && (e[0] === id || e[1] === id);
        p.classList.toggle("lit", hit);
        if (hit) near.add(e[0] === id ? e[1] : e[0]);
      });
      svg.querySelectorAll(".n").forEach((n) => { n.classList.toggle("near", near.has(n.dataset.id)); n.classList.toggle("lit", n.dataset.id === id); });
      document.querySelectorAll(".rail li[data-node]").forEach((li) => li.classList.toggle("lit", li.dataset.node === id));
      if (!id || !withTip || !pos[id]) { tip.classList.remove("on"); return; }
      const n = N[id], p = pos[id], scale = graph.clientWidth / W;
      tip.innerHTML = `<b>${esc(n.l)}</b><span>${esc(n.d)}</span>`;
      tip.classList.add("on");
      // Beside the dot, on the side with more room, so it covers neither band's edges.
      const tw = tip.offsetWidth, th = tip.offsetHeight, px = p.x * scale, right = px < graph.clientWidth / 2;
      tip.style.left = (right ? px + 13 : px - tw - 13) + "px";
      tip.style.top = Math.max(0, p.y * scale - th / 2) + "px";
    };
    svg.addEventListener("pointerover", (ev) => { const n = ev.target.closest(".n"); if (n) light(n.dataset.id, true); });
    svg.addEventListener("pointerleave", () => light(null));
    svg.addEventListener("focusin", (ev) => { const n = ev.target.closest(".n"); if (n) light(n.dataset.id, true); });
    svg.addEventListener("focusout", () => light(null));
    for (const el of document.querySelectorAll(".rail [data-node]")) {
      el.addEventListener("pointerenter", () => light(el.dataset.node, true));
      el.addEventListener("pointerleave", () => light(null));
    }
  }

  // ---- the flow: headline theorems are open cards; every other declaration is a row that opens
  // in place, and a "built from" name opens a copy of that definition under the declaration using it
  const P = JSON.parse($("preview").textContent);
  const D = $("decls"), toc = document.querySelector(".toc");
  const cards = new Map(Array.from(D.querySelectorAll(".decl")).map((d) => [d.id, d]));
  const all = Array.from(cards.values());
  const hay = new Map(all.map((d) => [d.id, d.textContent.toLowerCase()]));
  const sections = Array.from(D.querySelectorAll(".dsec"));
  const filter = $("filter"), expandAll = $("expand-all");
  const links = new Map(Array.from(document.querySelectorAll("#map a[data-for]")).map((a) => [a.dataset.for, a]));
  const keyOf = (d) => d.id || d.dataset.copyOf;

  function setOpen(d, on) {
    if (!d.classList.contains("row")) return;
    d.classList.toggle("open", on);
    d.querySelector(":scope > .dh .opener").setAttribute("aria-expanded", on);
    d.querySelector(":scope > .body").hidden = !on;
  }
  function copyOf(id) {
    const c = cards.get(id).cloneNode(true);
    c.removeAttribute("id");
    c.dataset.copyOf = id;
    for (const x of c.querySelectorAll("[id]")) x.removeAttribute("id");
    for (const b of c.querySelectorAll('.tg[aria-expanded="true"]')) b.setAttribute("aria-expanded", "false");
    for (const a of c.querySelectorAll(".bf-area")) a.replaceChildren();
    c.classList.remove("flash");
    setOpen(c, true);
    return c;
  }
  D.addEventListener("click", (ev) => {
    const tg = ev.target.closest(".tg");
    if (tg) {
      const area = tg.parentElement.nextElementSibling, id = tg.dataset.open;
      const open = Array.from(area.children).find((x) => x.dataset.copyOf === id);
      if (open) { open.remove(); tg.setAttribute("aria-expanded", "false"); }
      else if (cards.has(id)) {
        const c = copyOf(id), after = Array.from(area.children).find((x) => +x.dataset.order > +c.dataset.order);
        area.insertBefore(c, after || null);
        tg.setAttribute("aria-expanded", "true");
      }
      requestAnimationFrame(track);
      return;
    }
    const btn = ev.target.closest(".opener");
    if (!btn) return;
    const d = btn.closest(".decl");
    if (d.dataset.copyOf) {
      // Closing a copy puts it away and resets the name that opened it.
      const tgl = d.parentElement.previousElementSibling.querySelector(`.tg[data-open="${CSS.escape(d.dataset.copyOf)}"]`);
      if (tgl) tgl.setAttribute("aria-expanded", "false");
      d.remove();
    } else setOpen(d, !d.classList.contains("open"));
    requestAnimationFrame(track);
  });

  function flash(d) { d.classList.remove("flash"); void d.offsetWidth; d.classList.add("flash"); }
  // A link may name a declaration, or a constructor, field or derived instance inside one.
  const holder = (id) => cards.get(id) || (document.getElementById(id) || { closest: () => null }).closest(".decl:not([data-copy-of])");
  function go(id, push) {
    const d = holder(id);
    if (!d) return;
    if (d.closest("[hidden]") && filter.value) { filter.value = ""; apply(); }
    setOpen(d, true);
    if (push) try { history.pushState(null, "", "#" + id); } catch (e) {}
    d.scrollIntoView({ block: "start", behavior: reduce ? "auto" : "smooth" });
    flash(d);
  }
  document.addEventListener("click", (ev) => {
    const a = ev.target.closest('a[href^="#"]');
    if (!a) return;
    const id = decodeURIComponent(a.getAttribute("href").slice(1));
    if (!holder(id)) return;
    ev.preventDefault();
    go(id, true);
  });
  addEventListener("popstate", () => { const id = decodeURIComponent(location.hash.slice(1)); if (holder(id)) go(id, false); });

  expandAll.addEventListener("change", () => {
    for (const d of all) setOpen(d, expandAll.checked);
    requestAnimationFrame(track);
  });

  // ---- filter by name or text
  function apply() {
    const terms = filter.value.toLowerCase().split(/\s+/).filter(Boolean);
    for (const d of all) {
      const on = terms.every((t) => hay.get(d.id).includes(t));
      d.hidden = !on;
      const a = links.get(d.id);
      if (a) a.parentElement.hidden = !on;
    }
    for (const g of toc.querySelectorAll(".grp")) g.hidden = !g.querySelector("li:not([hidden])");
    for (const s of sections) s.hidden = terms.length > 0 && !s.querySelector(":scope > .decl:not([hidden])");
    $("none").hidden = !!toc.querySelector(".grp:not([hidden])");
  }
  filter.addEventListener("input", apply);
  filter.addEventListener("keydown", (ev) => { if (ev.key === "Escape") { filter.value = ""; apply(); } });

  const tocd = $("tocd"), wide = matchMedia("(min-width: 1240px)");
  const fit = () => { tocd.open = wide.matches; };
  fit();
  wide.addEventListener("change", fit);
  tocd.querySelector("summary").addEventListener("click", (ev) => { if (wide.matches) ev.preventDefault(); });

  // ---- where the reader is: the declaration at the reading line, marked in the map
  const LINE = 100;
  let here = null, ticking = false;
  function track() {
    ticking = false;
    // The last sections cannot scroll up to the reading line, so at the end of the page it drops.
    const end = innerHeight + scrollY >= document.documentElement.scrollHeight - 4;
    const line = end ? innerHeight * 0.6 : LINE;
    const sec = sections.filter((s) => !s.hidden && s.getBoundingClientRect().top <= line).pop();
    let cur = null;
    if (sec) for (const d of sec.querySelectorAll(".decl")) {
      if (d.offsetParent === null) continue;
      if (d.getBoundingClientRect().top <= line) cur = d; else break;
    }
    // A copy opened under a declaration reads as part of that declaration; above a section's first
    // declaration, its heading is the place.
    while (cur && cur.dataset.copyOf) cur = cur.parentElement.closest(".decl");
    const a = cur ? links.get(keyOf(cur))
      : sec ? toc.querySelector(`#map a.gh[href="#${CSS.escape(sec.querySelector("h2").id)}"]`) : null;
    if (a !== here) {
      if (here) here.classList.remove("here");
      here = a;
      if (here) {
        here.classList.add("here");
        if (wide.matches) {
          const r = here.getBoundingClientRect(), b = toc.getBoundingClientRect();
          if (r.top < b.top + 40 || r.bottom > b.bottom - 40) toc.scrollTop += r.top - b.top - b.height / 3;
        }
      }
    }
  }
  addEventListener("scroll", () => { if (!ticking) { ticking = true; requestAnimationFrame(track); } }, { passive: true });
  addEventListener("resize", () => requestAnimationFrame(track));

  // Hovering a declaration lights, in the map, the declarations it uses and those that use it.
  if (hoverable) for (const d of all) {
    d.addEventListener("pointerenter", () => {
      const rel = new Set([...d.dataset.uses.split(" "), ...d.dataset.usedBy.split(" ")].filter(Boolean));
      if (!rel.size) return;
      toc.classList.add("relating");
      for (const [id, a] of links) { a.classList.toggle("rel", rel.has(id)); a.classList.toggle("self", id === d.id); }
    });
    d.addEventListener("pointerleave", () => {
      toc.classList.remove("relating");
      for (const a of links.values()) a.classList.remove("rel", "self");
    });
  }

  requestAnimationFrame(track);
  if (location.hash && holder(decodeURIComponent(location.hash.slice(1)))) go(decodeURIComponent(location.hash.slice(1)), false);

  // ---- copy a declaration's full name
  document.addEventListener("click", (ev) => {
    const b = ev.target.closest("[data-copy]");
    if (!b) return;
    const done = () => { b.textContent = "copied"; setTimeout(() => { b.textContent = "copy"; }, 1200); };
    try { navigator.clipboard.writeText(b.dataset.copy).then(done, () => {}); } catch (e) {}
  });

  // ---- previews of the declarations a link names
  const pop = $("pop");
  let timer = null;
  function show(a) {
    const id = decodeURIComponent(a.getAttribute("href").slice(1)), p = P[id];
    if (!p || a.closest(".dh") || a.closest(".toc")) return;
    const say = p.c || p.d;
    pop.innerHTML = `<div class="ph">${esc(p.k)} <b>${esc(p.n)}</b>${p.l ? " · " + esc(p.l) : ""}</div>` + (say ? `<div>${esc(say)}</div>` : `<div class="ps">${esc(p.s)}</div>`);
    if (window.MathJax && MathJax.typesetPromise) MathJax.typesetPromise([pop]);
    const r = a.getBoundingClientRect();
    pop.classList.add("on");
    const pw = pop.offsetWidth, ph = pop.offsetHeight;
    const x = Math.min(Math.max(12, r.left), innerWidth - pw - 12);
    const y = r.bottom + 8 + ph < innerHeight ? r.bottom + 8 : r.top - ph - 8;
    pop.style.left = x + "px";
    pop.style.top = y + "px";
  }
  if (hoverable) {
    document.addEventListener("pointerover", (ev) => {
      const a = ev.target.closest('a[href^="#"]');
      if (!a) return;
      clearTimeout(timer);
      timer = setTimeout(() => show(a), 220);
    });
    document.addEventListener("pointerout", (ev) => {
      if (!ev.target.closest('a[href^="#"]')) return;
      clearTimeout(timer);
      pop.classList.remove("on");
    });
  }

  document.addEventListener("keydown", (ev) => {
    if (ev.key === "/" && !/^(INPUT|TEXTAREA|SELECT)$/.test(document.activeElement.tagName)) { ev.preventDefault(); filter.focus(); }
  });
})();

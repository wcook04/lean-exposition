import { StrictMode } from "react";
import { createRoot } from "react-dom/client";

import "@fontsource/stix-two-text/400.css";
import "@fontsource/stix-two-text/400-italic.css";
import "@fontsource/stix-two-text/500.css";
import "@fontsource/stix-two-text/600.css";
import "@fontsource-variable/source-sans-3/wght.css";
import "@fontsource-variable/source-sans-3/wght-italic.css";
import "@fontsource/jetbrains-mono/400.css";

import "./styles/tokens.css";
import "./styles/base.css";
// The parts every one of Will Cook's websites shares, copied unchanged; tokens.css maps their names.
import "./styles/family.css";
import "./reader/reader-content.css";
import "./figures/figures.css";
import "./app/app.css";
import "./home/hero.css";
// The selected instance's own styles, if it has any (the SK site has none).
import "@instance/theme";

import { App } from "./app/App";
import { prefetch } from "./app/prefetch";
import { parseRoute, reparseCurrentRoute } from "./app/router";
import { loadLibraryAddresses } from "./app/libraryAddress";

// A library paper reads its phrase addresses before the first route is used; the router parsed the
// address when it loaded, so it parses it again with the table.
await loadLibraryAddresses((import.meta.env.BASE_URL ?? "/").replace(/\/$/, ""));
reparseCurrentRoute();
prefetch(parseRoute(new URL(window.location.href)).view);

createRoot(document.getElementById("root")!).render(
  <StrictMode>
    <App />
  </StrictMode>,
);

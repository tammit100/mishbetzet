// Builds the single-file version of the app, which is what a Claude artifact needs.
// Usage:  node tools/build.js      ->  dist/mishbetzet.html
// It takes index.html and puts the local CSS and JS files inside it. Links to other sites stay as they are.
const fs = require("fs"), path = require("path");
const root = path.join(__dirname, "..");
const read = f => fs.readFileSync(path.join(root, f), "utf8").replace(/\r\n/g, "\n");
let html = read("index.html");
html = html.replace(/<link rel="stylesheet" href="(?!https?:)([^"]+)">/g, (m, f) => "<style>\n" + read(f) + "</style>");
html = html.replace(/<script src="(?!https?:)([^"]+)"><\/script>/g, (m, f) => {
  const js = read(f);
  if (/<\/script/i.test(js)) throw new Error(f + " contains </script, which would end the inline script early");
  return "<script>\n" + js + "</script>";
});
fs.mkdirSync(path.join(root, "dist"), { recursive: true });
fs.writeFileSync(path.join(root, "dist", "mishbetzet.html"), html);
console.log("dist/mishbetzet.html", Math.round(html.length / 1024) + " KB");

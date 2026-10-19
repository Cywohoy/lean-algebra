// Local preview and public hosting use the same WASM reader and regression suite.
process.env.BOOK_URL ||= 'http://127.0.0.1:8001/';
require('./BrowserReader.Tests.cjs');

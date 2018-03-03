</
  define p: output$=24;
  define q: output$=26;
  
  (alw(!p); next(q and !p)) or alw(!p)
/>
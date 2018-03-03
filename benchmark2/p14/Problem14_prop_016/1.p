</
  define p: output$=24;
  define q: output$=22;
  
  (alw(!p); next(q and !p)) or alw(!p)
/>
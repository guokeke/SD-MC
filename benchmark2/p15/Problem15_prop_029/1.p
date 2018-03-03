</
  define p: input$=1;
  define q: output$=22;
  
  !som(p) or (alw(!q and !p); next(p or (alw(q and !p);next (p or (alw(!q and !p);next ( p or (alw(q and !p); next (p or (alw(!q);next p)))))))))
/>
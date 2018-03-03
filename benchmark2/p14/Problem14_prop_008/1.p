</
  define p: input$=6;
  define q: input$=2;
  define r: output$=24;
  
  alw(!(p or !q and som(q)) or (alw(!r);next q))
/>
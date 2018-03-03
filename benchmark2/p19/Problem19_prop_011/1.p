</
  define p: input$=6;
  define q: output$=22;
  define r: output$=24;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>

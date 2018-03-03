</
  define p: output$=24;
  define q: input$=2;
  define r: output$=25;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>

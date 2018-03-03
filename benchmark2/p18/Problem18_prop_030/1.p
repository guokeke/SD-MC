</
  define p: input$=5;
  define q: output$=24;
  define r: output$=25;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>
